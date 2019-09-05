use sapling_crypto::bellman::pairing::ff::ScalarEngine;
use sapling_crypto::bellman::pairing::Engine;
use sapling_crypto::bellman::{ConstraintSystem, LinearCombination, SynthesisError};

use std::cmp::Eq;

use bit::Bit;
use OptionExt;

pub trait Gadget: Sized + Clone {
    type E: Engine;
    type Value: Clone;
    type Access: Clone + Eq;
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
