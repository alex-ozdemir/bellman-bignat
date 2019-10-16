use sapling_crypto::bellman::pairing::Engine;
use sapling_crypto::bellman::ConstraintSystem;

use CResult;
use hash::MaybeHashed;

pub mod int_set;
pub mod merkle;
pub mod rsa;

pub trait GenSet<E>
where
    E: Engine,
{
    type Digest;

    fn swap(&mut self, old: &[E::Fr], new: Vec<E::Fr>);

    /// Remove all of the `ns` from the set.
    fn swap_all<I, J>(&mut self, old: I, new: J)
    where
        I: IntoIterator<Item = Vec<E::Fr>>,
        J: IntoIterator<Item = Vec<E::Fr>>,
    {
        for (i, j) in old.into_iter().zip(new.into_iter()) {
            self.swap(i.as_slice(), j);
        }
    }

    fn digest(&self) -> Self::Digest;
}

pub trait CircuitGenSet : Sized {
    type E: Engine;
    fn swap_all<CS: ConstraintSystem<Self::E>>(
        self,
        cs: CS,
        removed_items: Vec<MaybeHashed<Self::E>>,
        inserted_items: Vec<MaybeHashed<Self::E>>,
    ) -> CResult<Self>;
}
