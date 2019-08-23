use sapling_crypto::bellman::{ConstraintSystem, LinearCombination, SynthesisError};
use sapling_crypto::bellman::pairing::Engine;
use sapling_crypto::bellman::pairing::ff::{Field, PrimeField, PrimeFieldRepr};

use usize_to_f;

use bit::{Bit, Bitvector};

pub struct Num<E: Engine> {
    pub num: LinearCombination<E>,
    pub value: Option<E::Fr>,
}

impl<E: Engine> Num<E> {
    pub fn new(value: Option<E::Fr>, num: LinearCombination<E>) -> Self {
        Self { value, num }
    }
    pub fn alloc<CS, F>(mut cs: CS, value: F) -> Result<Self, SynthesisError>
    where
        CS: ConstraintSystem<E>,
        F: FnOnce() -> Result<E::Fr, SynthesisError>,
    {
        let mut new_value = None;
        let var = cs.alloc(
            || "num",
            || {
                let tmp = value()?;

                new_value = Some(tmp);

                Ok(tmp)
            },
        )?;

        Ok(Num {
            value: new_value,
            num: LinearCombination::zero() + var,
        })
    }

    /// Compute the natural number represented by an array of limbs.
    /// The limbs are assumed to be based the `limb_width` power of 2.
    pub fn fits_in_bits<CS: ConstraintSystem<E>>(
        &self,
        mut cs: CS,
        n_bits: usize,
    ) -> Result<Bitvector<E>, SynthesisError> {
        let values: Option<Vec<bool>> = self.value.as_ref().map(|v| {
            let mut num = v.into_repr();
            (0..n_bits)
                .map(|_| {
                    let bit = num.is_odd();
                    num.shr(1);
                    bit
                })
                .collect()
        });
        let allocations: Vec<Bit<E>> = (1..n_bits)
            .map(|bit_i| {
                Bit::alloc(
                    cs.namespace(|| format!("bit{}", bit_i)),
                    values.as_ref().map(|vs| vs[bit_i]),
                )
            })
            .collect::<Result<Vec<_>, _>>()?;
        let sum_of_tail_bits = allocations
            .iter()
            .zip(1..n_bits)
            .fold(LinearCombination::zero(), |lc, (bit, bit_i)| {
                lc + (usize_to_f::<E::Fr>(2).pow(&[bit_i as u64]), &bit.bit)
            });
        let bit0_lc = LinearCombination::zero() + &self.num - &sum_of_tail_bits;
        cs.enforce(
            || "sum",
            |lc| lc + &bit0_lc,
            |lc| lc + CS::one() - &bit0_lc,
            |lc| lc,
        );
        let bits: Vec<LinearCombination<E>> = std::iter::once(bit0_lc)
            .chain(
                allocations
                    .into_iter()
                    .map(|a| LinearCombination::zero() + &a.bit),
            )
            .collect();
        Ok(Bitvector { values, bits })
    }
}
