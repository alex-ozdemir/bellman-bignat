use num_bigint::BigUint;
use sapling_crypto::bellman::pairing::Engine;
use sapling_crypto::bellman::{ConstraintSystem, LinearCombination, SynthesisError};

use bignat::BigNat;
use bit::{Bit, Bitvector};
use OptionExt;

pub trait Gadget<E: Engine>: Sized {
    type Value: Clone;
    type Params: Eq;
    fn alloc<F, CS: ConstraintSystem<E>>(
        cs: CS,
        value: F,
        params: &Self::Params,
    ) -> Result<Self, SynthesisError>
    where
        F: FnOnce() -> Result<Self::Value, SynthesisError>;
    fn wires(&self) -> Vec<LinearCombination<E>>;
    fn value(&self) -> Option<&Self::Value>;
    fn params(&self) -> &Self::Params;
    fn mux<CS: ConstraintSystem<E>>(
        mut cs: CS,
        s: &Bit<E>,
        i0: &Self,
        i1: &Self,
    ) -> Result<Self, SynthesisError> {
        let i0_wires = i0.wires();
        let i1_wires = i1.wires();
        if i0_wires.len() != i1_wires.len() || i0.params() != i1.params() {
            return Err(SynthesisError::Unsatisfiable);
        }
        let value: Option<Self::Value> = s.value.and_then(|b| {
            if b {
                i1.value().cloned()
            } else {
                i0.value().cloned()
            }
        });
        let out: Self = Self::alloc(
            cs.namespace(|| "out"),
            || Ok(value.grab()?.clone()),
            i0.params().clone(),
        )?;
        let out_wires = out.wires();
        if out_wires.len() != i0_wires.len() {
            return Err(SynthesisError::Unsatisfiable);
        }
        for (i, ((i0w, i1w), out_w)) in i0_wires
            .into_iter()
            .zip(i1_wires)
            .zip(out_wires)
            .enumerate()
        {
            cs.enforce(
                || format!("{}", i),
                |lc| lc + &s.bit,
                |lc| lc + &i1w - &i0w,
                |lc| lc + &out_w - &i0w,
            );
        }
        Ok(out)
    }

    fn assert_equal<CS: ConstraintSystem<E>>(
        mut cs: CS,
        i0: &Self,
        i1: &Self,
    ) -> Result<(), SynthesisError> {
        let i0_wires = i0.wires();
        let i1_wires = i1.wires();
        if i0_wires.len() != i1_wires.len() || i0.params() != i1.params() {
            return Err(SynthesisError::Unsatisfiable);
        }
        for (i, (i0w, i1w)) in i0_wires.into_iter().zip(i1_wires).enumerate() {
            cs.enforce(|| format!("{}", i), |lc| lc, |lc| lc, |lc| lc + &i1w - &i0w);
        }
        Ok(())
    }
}

pub trait CircuitSemiGroup<E: Engine> {
    type Elem: Clone + Gadget<E>;
    type Group: SemiGroup;
    fn group(&self) -> Option<&Self::Group>;
    fn op<CS: ConstraintSystem<E>>(
        &self,
        cs: CS,
        a: &Self::Elem,
        b: &Self::Elem,
    ) -> Result<Self::Elem, SynthesisError>;
    fn generator<CS: ConstraintSystem<E>>(&self) -> Self::Elem;
    fn identity<CS: ConstraintSystem<E>>(&self) -> Self::Elem;
    fn power_bin_rev<CS: ConstraintSystem<E>>(
        &self,
        mut cs: CS,
        base: &Self::Elem,
        mut exp: Bitvector<E>,
    ) -> Result<Self::Elem, SynthesisError> {
        if exp.bits.len() == 0 {
            Ok(self.identity::<CS>())
        } else {
            let square = self.op(cs.namespace(|| "square"), &base, &base)?;
            let select_bit = Bit {
                // Unwrap is safe b/c of `n_bits` check
                value: exp.values.as_mut().map(|vs| vs.pop().unwrap()),
                bit: exp.bits.pop().unwrap(),
            };
            let rec = self.power_bin_rev(cs.namespace(|| "rec"), &base, exp)?;
            let prod = self.op(cs.namespace(|| "prod"), &rec, &base)?;
            <Self::Elem as Gadget<E>>::mux(cs.namespace(|| "mux"), &select_bit, &rec, &prod)
        }
    }
    fn power<CS: ConstraintSystem<E>>(
        &self,
        mut cs: CS,
        b: &Self::Elem,
        e: &BigNat<E>,
    ) -> Result<Self::Elem, SynthesisError> {
        let exp_bin_rev = e.decompose(cs.namespace(|| "exp decomp"))?.reversed();
        self.power_bin_rev(cs.namespace(|| "binary exp"), &b, exp_bin_rev)
    }
}

pub trait SemiGroup {
    type Elem: Clone;
    fn op(&self, a: &Self::Elem, b: &Self::Elem) -> Self::Elem;
    fn identity(&self) -> Self::Elem;
    fn generator(&self) -> Self::Elem;
    fn power(&self, b: &Self::Elem, e: &BigUint) -> Self::Elem {
        let mut acc = self.identity();
        let bits = e.to_str_radix(2);
        for bit in bits.bytes() {
            match bit {
                b'0' => {
                    acc = self.op(&acc, &acc);
                }
                b'1' => {
                    acc = self.op(&self.op(&acc, &acc), &acc);
                }
                _ => unreachable!(),
            }
        }
        acc
    }
}
