// (mostly from franklin-crypto)
use sapling_crypto::bellman::{ConstraintSystem, LinearCombination, SynthesisError};
use sapling_crypto::bellman::pairing::Engine;
use sapling_crypto::bellman::pairing::ff::Field;

use OptionExt;

/// A representation of a bit
pub struct Bit<E: Engine> {
    /// The linear combination which constrain the value of the bit
    pub bit: LinearCombination<E>,
    /// The value of the bit (filled at witness-time)
    pub value: Option<bool>,
}

/// A representation of a bit-vector
pub struct Bitvector<E: Engine> {
    /// The linear combination which constrain the values of the bits
    pub bits: Vec<LinearCombination<E>>,
    /// The value of the bits (filled at witness-time)
    pub values: Option<Vec<bool>>,
}

impl<E: Engine> Bitvector<E> {
    /// Reverse the order of the bits
    pub fn reversed(mut self) -> Self {
        self.values.as_mut().map(|v| v.reverse());
        self.bits.reverse();
        self
    }
    /// Keep only the first `n` bits.
    pub fn truncate(mut self, n: usize) -> Self {
        self.values.as_mut().map(|v| v.truncate(n));
        self.bits.truncate(n);
        self
    }
}

impl<E: Engine> Bit<E> {
    /// Allocate a variable in the constraint system which can only be a
    /// boolean value.
    pub fn alloc<CS>(mut cs: CS, value: Option<bool>) -> Result<Self, SynthesisError>
    where
        E: Engine,
        CS: ConstraintSystem<E>,
    {
        let var = cs.alloc(
            || "boolean",
            || {
                if *value.grab()? {
                    Ok(E::Fr::one())
                } else {
                    Ok(E::Fr::zero())
                }
            },
        )?;

        // Constrain: (1 - a) * a = 0
        // This constrains a to be either 0 or 1.
        cs.enforce(
            || "boolean constraint",
            |lc| lc + CS::one() - var,
            |lc| lc + var,
            |lc| lc,
        );

        Ok(Self {
            bit: LinearCombination::zero() + var,
            value,
        })
    }
}
