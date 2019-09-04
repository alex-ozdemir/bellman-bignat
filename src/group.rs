use num_bigint::BigUint;
use num_traits::One;
use sapling_crypto::bellman::pairing::Engine;
use sapling_crypto::bellman::{ConstraintSystem, LinearCombination, SynthesisError};

use std::fmt::Debug;

use bignat::{BigNat, BigNatParams};
use bit::{Bit, Bitvector};
use OptionExt;

pub trait Gadget<E: Engine>: Sized + Clone {
    type Value: Clone;
    type Access: Clone + Eq;
    type Params: Clone + Eq + Debug;
    fn alloc<CS: ConstraintSystem<E>>(
        cs: CS,
        value: Option<&Self::Value>,
        access: Self::Access,
        params: &Self::Params,
    ) -> Result<Self, SynthesisError>;
    fn wires(&self) -> Vec<LinearCombination<E>>;
    fn wire_values(&self) -> Option<Vec<E::Fr>>;
    fn value(&self) -> Option<&Self::Value>;
    fn access(&self) -> &Self::Access;
    fn params(&self) -> &Self::Params;
    fn inputize<CS: ConstraintSystem<E>>(&self, mut cs: CS) -> Result<(), SynthesisError> {
        let values = self.wire_values();
        for (i, w) in self.wires().into_iter().enumerate() {
            let mut cs = cs.namespace(|| format!("{}", i));
            let in_ = cs.alloc_input(|| "in", || Ok(values.as_ref().grab()?[i].clone()))?;
            cs.enforce(
                || "eq",
                |lc| lc,
                |lc| lc,
                |lc| lc + in_ - &w,
            );
        }
        Ok(())
    }
    fn mux<CS: ConstraintSystem<E>>(
        mut cs: CS,
        s: &Bit<E>,
        i0: &Self,
        i1: &Self,
    ) -> Result<Self, SynthesisError> {
        let i0_wires = i0.wires();
        let i1_wires = i1.wires();
        if i0_wires.len() != i1_wires.len() || i0.params() != i1.params() {
            eprintln!("mux error: Params differ!");
            return Err(SynthesisError::Unsatisfiable);
        }
        let value: Option<&Self::Value> = s
            .value
            .and_then(|b| if b { i1.value() } else { i0.value() });
        if i0.access() != i1.access() {
            eprintln!("mux error: Accesses differ!");
            return Err(SynthesisError::Unsatisfiable);
        }
        let out: Self = Self::alloc(
            cs.namespace(|| "out"),
            value,
            i0.access().clone(),
            i0.params(),
        )?;
        let out_wires = out.wires();
        if out_wires.len() != i0_wires.len() {
            eprintln!("mux error: output has a bad number of wires!");
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

pub trait CircuitSemiGroup<E: Engine>: Gadget<E> {
    type Elem: Clone + Gadget<E>;
    type Group: SemiGroup;
    fn op<CS: ConstraintSystem<E>>(
        &self,
        cs: CS,
        a: &Self::Elem,
        b: &Self::Elem,
    ) -> Result<Self::Elem, SynthesisError>;
    fn generator(&self) -> Self::Elem;
    fn identity(&self) -> Self::Elem;
    fn group(&self) -> Option<&Self::Group>;
    fn elem_params(p: &<Self as Gadget<E>>::Params) -> <Self::Elem as Gadget<E>>::Params;
    fn power_bin_rev<CS: ConstraintSystem<E>>(
        &self,
        mut cs: CS,
        base: &Self::Elem,
        mut exp: Bitvector<E>,
    ) -> Result<Self::Elem, SynthesisError> {
        if exp.bits.len() == 0 {
            Ok(self.identity())
        } else {
            let square = self.op(cs.namespace(|| "square"), &base, &base)?;
            let select_bit = Bit {
                // Unwrap is safe b/c of `n_bits` check
                value: exp.values.as_mut().map(|vs| vs.pop().unwrap()),
                bit: exp.bits.pop().unwrap(),
            };
            let rec = self.power_bin_rev(cs.namespace(|| "rec"), &square, exp)?;
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

pub trait SemiGroup: Clone {
    type Elem: Clone + Debug;
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
                    acc = self.op(&self.op(&acc, &acc), &b);
                }
                _ => unreachable!(),
            }
        }
        acc
    }
}

// TODO (aozdemir) mod out by the <-1> subgroup.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RsaGroup {
    pub g: BigUint,
    pub m: BigUint,
}

impl SemiGroup for RsaGroup {
    type Elem = BigUint;

    fn op(&self, a: &BigUint, b: &BigUint) -> BigUint {
        a * b % &self.m
    }

    fn identity(&self) -> BigUint {
        BigUint::one()
    }

    fn generator(&self) -> BigUint {
        self.g.clone()
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CircuitRsaGroupParams {
    pub limb_width: usize,
    pub n_limbs: usize,
}

#[derive(Clone)]
pub struct CircuitRsaGroup<E: Engine> {
    pub g: BigNat<E>,
    pub m: BigNat<E>,
    pub id: BigNat<E>,
    pub value: Option<RsaGroup>,
    pub params: CircuitRsaGroupParams,
}

impl<E: Engine> std::cmp::PartialEq for CircuitRsaGroup<E> {
    fn eq(&self, other: &Self) -> bool {
        self.g == other.g
            && self.m == other.m
            && self.id == other.id
            && self.value == other.value
            && self.params == other.params
    }
}
impl<E: Engine> std::cmp::Eq for CircuitRsaGroup<E> {}

impl<E: Engine> Gadget<E> for CircuitRsaGroup<E> {
    type Value = RsaGroup;
    type Params = CircuitRsaGroupParams;
    type Access = ();
    fn alloc<CS: ConstraintSystem<E>>(
        mut cs: CS,
        value: Option<&Self::Value>,
        _access: (),
        params: &Self::Params,
    ) -> Result<Self, SynthesisError> {
        let value = value.cloned();
        let g = <BigNat<E> as Gadget<E>>::alloc(
            cs.namespace(|| "g"),
            value.as_ref().map(|v| &v.g),
            (),
            &BigNatParams::new(params.limb_width, params.n_limbs),
        )?;
        let m = <BigNat<E> as Gadget<E>>::alloc(
            cs.namespace(|| "m"),
            value.as_ref().map(|v| &v.m),
            (),
            &BigNatParams::new(params.limb_width, params.n_limbs),
        )?;
        let one = BigUint::one();
        let id = <BigNat<E> as Gadget<E>>::alloc(
            cs.namespace(|| "id"),
            value.as_ref().map(|_| &one),
            (),
            &BigNatParams::new(params.limb_width, params.n_limbs),
        )?;
        Ok(Self {
            g,
            m,
            id,
            value,
            params: params.clone(),
        })
    }
    fn wires(&self) -> Vec<LinearCombination<E>> {
        let mut wires = self.g.wires();
        wires.extend(self.m.wires());
        wires
    }
    fn wire_values(&self) -> Option<Vec<E::Fr>> {
        let mut vs = self.g.wire_values();
        vs.as_mut().map(|vs| self.m.wire_values().map(|vs2| vs.extend(vs2)));
        vs
    }
    fn value(&self) -> Option<&Self::Value> {
        self.value.as_ref()
    }
    fn params(&self) -> &Self::Params {
        &self.params
    }
    fn access(&self) -> &() {
        &()
    }
}

impl<E: Engine> CircuitSemiGroup<E> for CircuitRsaGroup<E> {
    type Elem = BigNat<E>;
    type Group = RsaGroup;
    fn op<CS: ConstraintSystem<E>>(
        &self,
        cs: CS,
        a: &BigNat<E>,
        b: &BigNat<E>,
    ) -> Result<Self::Elem, SynthesisError> {
        a.mult_mod(cs, b, &self.m).map(|(_, r)| r)
    }
    fn elem_params(p: &<Self as Gadget<E>>::Params) -> <Self::Elem as Gadget<E>>::Params {
        BigNatParams::new(p.limb_width, p.n_limbs)
    }
    fn group(&self) -> Option<&Self::Group> {
        self.value.as_ref()
    }
    fn generator(&self) -> Self::Elem {
        self.g.clone()
    }
    fn identity(&self) -> Self::Elem {
        self.id.clone()
    }
}
