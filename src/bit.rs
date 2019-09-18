// (mostly from franklin-crypto)
use sapling_crypto::bellman::pairing::ff::Field;
use sapling_crypto::bellman::pairing::Engine;
use sapling_crypto::bellman::{ConstraintSystem, LinearCombination, SynthesisError};
use sapling_crypto::circuit::boolean::Boolean;

use std::fmt::{self, Formatter, Display};

use OptionExt;

#[derive(Clone)]
/// A representation of a bit
pub struct Bit<E: Engine> {
    /// The linear combination which constrain the value of the bit
    pub bit: LinearCombination<E>,
    /// The value of the bit (filled at witness-time)
    pub value: Option<bool>,
}

#[derive(Clone)]
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

    pub fn get(&self, i: usize) -> Option<Bit<E>> {
        self.bits.get(i).map(|lc| {
            Bit {
                bit: lc.clone(),
                value: self.values.as_ref().map(|vs| vs[i].clone()),
            }
        })
    }

    pub fn shr(mut self, i: usize) -> Self {
        self.values.as_mut().map(|v| {
            v.drain(0..i);
        });
        self.bits.drain(0..i);
        self
    }

    pub fn shl(mut self, i: usize) -> Self {
        self.values.as_mut().map(|v| {
            v.splice(0..0, std::iter::repeat(false).take(i));
        });
        self.bits.splice(0..0, std::iter::repeat(LinearCombination::zero()).take(i));
        self
    }

    pub fn split_off(&mut self, n_bits: usize) -> Bitvector<E> {
        let bits = self.bits.split_off(n_bits);
        let values = self.values.as_mut().map(|vs| vs.split_off(n_bits));
        Bitvector {
            bits,
            values,

        }
    }

    pub fn pop(&mut self) -> Option<Bit<E>> {
        if self.bits.len() > 0 {
            Some(Bit::new(
                self.bits.pop().unwrap(),
                self.values.as_mut().map(|vs| vs.pop().unwrap()),
            ))
        } else {
            None
        }
    }

    pub fn push(&mut self, mut b: Bit<E>) {
        self.values.as_mut().map(|vs| b.value.take().map(|v| vs.push(v)));
        self.bits.push(b.bit);
    }

    pub fn insert(&mut self, i: usize, mut b: Bit<E>) {
        self.values.as_mut().map(|vs| b.value.take().map(|v| vs.insert(i, v)));
        self.bits.insert(i, b.bit);
    }

    pub fn append(&mut self, mut other: Self) {
        let ovs = other.values.take();
        self.bits.extend(other.bits.into_iter());
        self.values.as_mut().map(|vs| ovs.map(|ovs| vs.extend(ovs.into_iter())));
    }

    pub fn into_bits(mut self) -> Vec<Bit<E>> {
        let vs = self.values.take();
        self.bits.into_iter().enumerate().map(|(i, b)| Bit {
            bit: b,
            value: vs.as_ref().map(|vs| vs[i]),
        }).collect()
    }

    pub fn from_bits(bs: Vec<Bit<E>>) -> Self {
        let mut bits = Vec::new();
        let mut values = Some(Vec::new());
        for mut b in bs {
            let v = b.value.take();
            bits.push(b.bit);
            values = values.take().and_then(|mut vs| v.map(|v| {
                vs.push(v);
                vs
            }));
        }
        Self {
            bits,
            values,
        }
    }
}

impl<E: Engine> Bit<E> {
    /// Allocate a variable in the constraint system which can only be a
    /// boolean value.
    pub fn alloc<CS>(mut cs: CS, value: Option<bool>) -> Result<Self, SynthesisError>
    where
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

    pub fn constrain_value<CS>(&self, mut cs: CS, value: bool)
    where
        CS: ConstraintSystem<E>,
    {
        cs.enforce(
            || format!("is {}", value),
            |lc| lc,
            |lc| lc,
            |lc| {
                if value {
                    lc + &self.bit - CS::one()
                } else {
                    lc + &self.bit
                }
            },
        );
    }

    pub fn new(bit: LinearCombination<E>, value: Option<bool>) -> Self {
        Self {
            bit,
            value,
        }
    }

    pub fn from_sapling<CS: ConstraintSystem<E>>(b: Boolean) ->  Self {
        Self::new(
            b.lc(CS::one(), E::Fr::one()),
            b.get_value(),
        )
    }

    pub fn not<CS: ConstraintSystem<E>>(&self) -> Self {
        Self::new(
            LinearCombination::zero() + CS::one() - &self.bit,
            self.value.clone().map(|b| !b),
        )
    }

    pub fn new_false<CS: ConstraintSystem<E>>() -> Self {
        Self::new(LinearCombination::zero(), Some(false))
    }

    pub fn new_true<CS: ConstraintSystem<E>>() -> Self {
        Self::new(LinearCombination::zero() + CS::one(), Some(true))
    }
}


impl<E: Engine> Display for Bitvector<E> {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        match self.values.as_ref() {
            Some(vs) =>
                write!(f, "Bitvector({})", vs.into_iter().map(|b| if *b { "1" } else {"0"}).collect::<Vec<_>>().concat()),
            None => write!(f, "Bitvector(len {})", self.bits.len()),
        }
    }
}
