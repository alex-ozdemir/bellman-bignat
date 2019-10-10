use sapling_crypto::bellman::pairing::ff::Field;
use sapling_crypto::poseidon::{poseidon_hash, PoseidonEngine, PoseidonHashParams, QuinticSBox};

use std::rc::Rc;

pub trait Hasher<F: Field>: Clone {
    fn hash(&self, inputs: &[F]) -> F;
}

pub struct Poseidon<E>
where
    E: PoseidonEngine<SBox = QuinticSBox<E>>,
{
    pub params: Rc<E::Params>,
}

impl<E> Clone for Poseidon<E>
where
    E: PoseidonEngine<SBox = QuinticSBox<E>>,
{
    fn clone(&self) -> Self {
        Self {
            params: self.params.clone(),
        }
    }
}

impl<E> Hasher<E::Fr> for Poseidon<E>
where
    E: PoseidonEngine<SBox = QuinticSBox<E>>,
{
    fn hash(&self, inputs: &[E::Fr]) -> E::Fr {
        assert_eq!(self.params.output_len(), 1);
        poseidon_hash::<E>(&self.params, inputs).pop().unwrap()
    }
}

pub mod circuit {
    use sapling_crypto::bellman::pairing::Engine;
    use sapling_crypto::bellman::ConstraintSystem;
    use sapling_crypto::circuit::num::AllocatedNum;
    use sapling_crypto::circuit::poseidon_hash::poseidon_hash;
    use sapling_crypto::poseidon::{PoseidonEngine, PoseidonHashParams, QuinticSBox};
    use CResult;

    use std::clone::Clone;
    use std::rc::Rc;

    pub trait CircuitHasher<E: Engine>: Clone {
        fn hash<CS: ConstraintSystem<E>>(
            &self,
            cs: CS,
            inputs: &[AllocatedNum<E>],
        ) -> CResult<AllocatedNum<E>>;
    }

    pub struct CircuitPoseidon<E>
    where
        E: PoseidonEngine<SBox = QuinticSBox<E>>,
    {
        pub params: Rc<E::Params>,
    }

    impl<E> Clone for CircuitPoseidon<E>
    where
        E: PoseidonEngine<SBox = QuinticSBox<E>>,
    {
        fn clone(&self) -> Self {
            Self {
                params: self.params.clone(),
            }
        }
    }

    impl<E> CircuitHasher<E> for CircuitPoseidon<E>
    where
        E: PoseidonEngine<SBox = QuinticSBox<E>>,
    {
        fn hash<CS: ConstraintSystem<E>>(
            &self,
            cs: CS,
            inputs: &[AllocatedNum<E>],
        ) -> CResult<AllocatedNum<E>> {
            assert_eq!(self.params.output_len(), 1);
            Ok(poseidon_hash::<E, CS>(cs, inputs, &self.params)?
                .pop()
                .unwrap())
        }
    }
}
