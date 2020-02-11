use sapling_crypto::bellman::pairing::ff::ScalarEngine;
use sapling_crypto::bellman::pairing::Engine;
use sapling_crypto::bellman::{ConstraintSystem, LinearCombination, SynthesisError};
use sapling_crypto::circuit::num::AllocatedNum;

use hash::circuit::CircuitHasher;

use super::bit::Bit;
use OptionExt;

pub trait Gadget: Sized + Clone {
    type E: Engine;
    type Value: Clone;
    type Access: Clone;
    type Params: Clone;
    fn alloc<CS: ConstraintSystem<Self::E>>(
        cs: CS,
        value: Option<&Self::Value>,
        access: Self::Access,
        params: &Self::Params,
    ) -> Result<Self, SynthesisError>;
    fn wires(&self) -> Vec<LinearCombination<Self::E>>;
    fn wire_values(&self) -> Option<Vec<<Self::E as ScalarEngine>::Fr>>;
    fn value(&self) -> Option<&Self::Value>;
    fn access(&self) -> &Self::Access;
    fn params(&self) -> &Self::Params;
    fn inputize<CS: ConstraintSystem<Self::E>>(&self, mut cs: CS) -> Result<(), SynthesisError> {
        let values = self.wire_values();
        for (i, w) in self.wires().into_iter().enumerate() {
            let mut cs = cs.namespace(|| format!("{}", i));
            let in_ = cs.alloc_input(|| "in", || Ok(values.as_ref().grab()?[i].clone()))?;
            cs.enforce(|| "eq", |lc| lc, |lc| lc, |lc| lc + in_ - &w);
        }
        Ok(())
    }

    fn inputize_hash<CS: ConstraintSystem<Self::E>, H: CircuitHasher<E = Self::E>>(&self, mut cs: CS, hasher: &H) -> Result<AllocatedNum<Self::E>, SynthesisError> {
        let nums = self.as_nums(cs.namespace(|| "to nums"))?;
        let hash = hasher.allocate_hash(cs.namespace(|| "hash"), &nums)?;
        let in_ = cs.alloc_input(|| "input", || hash.get_value().ok_or(SynthesisError::AssignmentMissing))?;
        cs.enforce(|| "eq", |lc| lc, |lc| lc, |lc| lc + in_ - hash.get_variable());
        Ok(hash)
    }

    fn as_nums<CS: ConstraintSystem<Self::E>>(&self, mut cs: CS) -> Result<Vec<AllocatedNum<Self::E>>, SynthesisError> {
        let wires = self.wires();
        let wire_values = self.wire_values();
        wires.into_iter().enumerate().map(|(i, w)| {
            let n = AllocatedNum::alloc(cs.namespace(|| format!("wire {}", i)), || Ok(wire_values.grab()?[i]))?;
            cs.enforce(|| format!("wire eq {}", i), |lc| lc, |lc| lc, |lc| lc + &w - n.get_variable());
            Ok(n)
        }).collect()
    }

    /// Returns `i0` if `s` is false, otherwise `i1`.
    fn mux<CS: ConstraintSystem<Self::E>>(
        mut cs: CS,
        s: &Bit<Self::E>,
        i0: &Self,
        i1: &Self,
    ) -> Result<Self, SynthesisError> {
        let i0_wires = i0.wires();
        let i1_wires = i1.wires();
        if i0_wires.len() != i1_wires.len() {
            eprintln!("mux error: wires differ!");
            return Err(SynthesisError::Unsatisfiable);
        }
        let value: Option<&Self::Value> = s
            .value
            .and_then(|b| if b { i1.value() } else { i0.value() });
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
    /// Builds a mux tree. The first bit is taken as the highest order.
    fn mux_tree<'a, CS: ConstraintSystem<Self::E>>(
        mut cs: CS,
        mut select_bits: impl Iterator<Item = &'a Bit<Self::E>> + Clone,
        inputs: &[Self],
    ) -> Result<Self, SynthesisError> {
        if let Some(bit) = select_bits.next() {
            if inputs.len() & 1 != 0 {
                return Err(SynthesisError::Unsatisfiable);
            }
            let left_half = &inputs[..(inputs.len() / 2)];
            let right_half = &inputs[(inputs.len() / 2)..];
            let left = Gadget::mux_tree(cs.namespace(|| "left"), select_bits.clone(), left_half)?;
            let right = Gadget::mux_tree(cs.namespace(|| "right"), select_bits, right_half)?;
            Gadget::mux(cs.namespace(|| "join"), bit, &left, &right)
        } else {
            if inputs.len() != 1 {
                return Err(SynthesisError::Unsatisfiable);
            }
            Ok(inputs[0].clone())
        }
    }

    /// Switches `i0` and `i1` iff `s`.
    fn switch<CS: ConstraintSystem<Self::E>>(
        mut cs: CS,
        s: &Bit<Self::E>,
        i0: &Self,
        i1: &Self,
    ) -> Result<(Self, Self), SynthesisError> {
        let not_s = s.not::<CS>();
        let o0 = Gadget::mux(cs.namespace(|| "out 0"), s, i0, i1)?;
        let o1 = Gadget::mux(cs.namespace(|| "out 1"), &not_s, i0, i1)?;
        Ok((o0, o1))
    }

    fn assert_equal<CS: ConstraintSystem<Self::E>>(
        mut cs: CS,
        i0: &Self,
        i1: &Self,
    ) -> Result<(), SynthesisError> {
        let i0_wires = i0.wires();
        let i1_wires = i1.wires();
        if i0_wires.len() != i1_wires.len() {
            return Err(SynthesisError::Unsatisfiable);
        }
        for (i, (i0w, i1w)) in i0_wires.into_iter().zip(i1_wires).enumerate() {
            cs.enforce(|| format!("{}", i), |lc| lc, |lc| lc, |lc| lc + &i1w - &i0w);
        }
        Ok(())
    }
}
