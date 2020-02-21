use sapling_crypto::bellman::pairing::ff::PrimeField;
use sapling_crypto::bellman::pairing::Engine;
use sapling_crypto::bellman::ConstraintSystem;

use hash::circuit::MaybeHashed;
use CResult;

pub mod int_set;
pub mod merkle;
pub mod rsa;

pub trait GenSet<F>
where
    F: PrimeField,
{
    type Digest;

    fn swap(&mut self, old: &[F], new: Vec<F>);

    /// Remove all of the `ns` from the set.
    fn swap_all<I, J>(&mut self, old: I, new: J)
    where
        I: IntoIterator<Item = Vec<F>>,
        J: IntoIterator<Item = Vec<F>>,
    {
        for (i, j) in old.into_iter().zip(new.into_iter()) {
            self.swap(i.as_slice(), j);
        }
    }

    fn digest(&mut self) -> Self::Digest;
}

pub trait CircuitGenSet: Sized {
    type E: Engine;
    fn swap_all<CS: ConstraintSystem<Self::E>>(
        self,
        cs: CS,
        removed_items: Vec<MaybeHashed<Self::E>>,
        inserted_items: Vec<MaybeHashed<Self::E>>,
    ) -> CResult<Self>;
    fn verify_swap_all<CS: ConstraintSystem<Self::E>>(
        self,
        cs: CS,
        removed_items: Vec<MaybeHashed<Self::E>>,
        inserted_items: Vec<MaybeHashed<Self::E>>,
        result: Self,
    ) -> CResult<()>;
}
