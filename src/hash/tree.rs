use sapling_crypto::bellman::pairing::ff::Field;
use sapling_crypto::bellman::pairing::Engine;
use sapling_crypto::jubjub::JubjubEngine;
use sapling_crypto::poseidon::{poseidon_hash, PoseidonEngine, PoseidonHashParams, QuinticSBox};

use std::marker::PhantomData;
use std::rc::Rc;

pub trait Hasher: Clone {
    type F: Field;
    fn hash(&self, inputs: &[Self::F]) -> Self::F;
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

impl<E> Hasher for Poseidon<E>
where
    E: PoseidonEngine<SBox = QuinticSBox<E>>,
{
    type F = E::Fr;

    fn hash(&self, inputs: &[E::Fr]) -> E::Fr {
        assert_eq!(self.params.output_len(), 1);
        poseidon_hash::<E>(&self.params, inputs).pop().unwrap()
    }
}

pub struct Pedersen<E>
where
    E: JubjubEngine,
{
    params: Rc<E::Params>,
}

impl<E> Clone for Pedersen<E>
where
    E: JubjubEngine,
{
    fn clone(&self) -> Self {
        Self {
            params: self.params.clone(),
        }
    }
}

impl<E: JubjubEngine> Hasher for Pedersen<E> {
    type F = E::Fr;
    fn hash(&self, inputs: &[E::Fr]) -> E::Fr {
        use sapling_crypto::bellman::pairing::ff::PrimeField;
        use sapling_crypto::pedersen_hash::pedersen_hash;
        use sapling_crypto::pedersen_hash::Personalization;
        let mut bits: Vec<bool> = Vec::new();
        for i in inputs {
            bits.extend(
                i.into_repr()
                    .as_ref()
                    .iter()
                    .flat_map(|w| (0..64).map(move |i| (*w & (1 << i)) != 0))
                    .take(E::Fr::NUM_BITS as usize),
            )
        }
        pedersen_hash::<E, _>(Personalization::NoteCommitment, bits, &self.params)
            .into_xy()
            .0
    }
}

pub struct BabyPedersen<E>
where
    E: sapling_crypto::babyjubjub::JubjubEngine,
{
    params: Rc<E::Params>,
}

impl<E> Clone for BabyPedersen<E>
where
    E: sapling_crypto::babyjubjub::JubjubEngine,
{
    fn clone(&self) -> Self {
        Self {
            params: self.params.clone(),
        }
    }
}

impl<E: sapling_crypto::babyjubjub::JubjubEngine> Hasher for BabyPedersen<E> {
    type F = E::Fr;
    fn hash(&self, inputs: &[E::Fr]) -> E::Fr {
        use sapling_crypto::baby_pedersen_hash::pedersen_hash;
        use sapling_crypto::baby_pedersen_hash::Personalization;
        use sapling_crypto::bellman::pairing::ff::PrimeField;
        let mut bits: Vec<bool> = Vec::new();
        for i in inputs {
            bits.extend(
                i.into_repr()
                    .as_ref()
                    .iter()
                    .flat_map(|w| (0..64).map(move |i| (*w & (1 << i)) != 0))
                    .take(E::Fr::NUM_BITS as usize),
            )
        }
        pedersen_hash::<E, _>(Personalization::NoteCommitment, bits, &self.params)
            .into_xy()
            .0
    }
}

pub struct Mimc<E>
where
    E: Engine,
{
    _params: PhantomData<E>,
}

impl<E> Mimc<E> where E: Engine
{
    fn new() -> Self {
        Self {
            _params: PhantomData::<E>::default(),
        }
    }
}

impl<E> Clone for Mimc<E>
where
    E: Engine,
{
    fn clone(&self) -> Self {
        Self {
            _params: self._params.clone(),
        }
    }
}

impl<E: Engine> Hasher for Mimc<E> {
    type F = E::Fr;
    fn hash(&self, inputs: &[E::Fr]) -> E::Fr {
        use hash::mimc;
        mimc::helper::hash(inputs)
    }
}

pub struct PoseidonMimc<E>
where
    E: PoseidonEngine<SBox = QuinticSBox<E>>,
{
    pub params: Rc<E::Params>,
}

impl<E> Clone for PoseidonMimc<E>
where
    E: PoseidonEngine<SBox = QuinticSBox<E>>,
{
    fn clone(&self) -> Self {
        Self {
            params: self.params.clone(),
        }
    }
}

pub mod circuit {
    use super::{BabyPedersen, Hasher, Pedersen, Poseidon, Mimc};
    use sapling_crypto::alt_babyjubjub::AltJubjubBn256;
    use sapling_crypto::bellman::pairing::bn256::Bn256;
    use sapling_crypto::bellman::pairing::ff::PrimeField;
    use sapling_crypto::bellman::pairing::Engine;
    use sapling_crypto::bellman::{Circuit, ConstraintSystem};
    use sapling_crypto::circuit::num::AllocatedNum;
    use sapling_crypto::circuit::poseidon_hash::poseidon_hash;
    use sapling_crypto::group_hash::Keccak256Hasher;
    use sapling_crypto::jubjub::JubjubEngine;
    use sapling_crypto::poseidon::bn256::Bn256PoseidonParams;
    use sapling_crypto::poseidon::{PoseidonEngine, PoseidonHashParams, QuinticSBox};
    use CResult;

    use std::clone::Clone;
    use std::rc::Rc;

    pub trait CircuitHasher: Clone {
        type E: Engine;
        fn allocate_hash<CS: ConstraintSystem<Self::E>>(
            &self,
            cs: CS,
            inputs: &[AllocatedNum<Self::E>],
        ) -> CResult<AllocatedNum<Self::E>>;
    }

    impl<E> CircuitHasher for Poseidon<E>
    where
        E: PoseidonEngine<SBox = QuinticSBox<E>>,
    {
        type E = E;
        fn allocate_hash<CS: ConstraintSystem<E>>(
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

    impl<E> CircuitHasher for Pedersen<E>
    where
        E: JubjubEngine,
    {
        type E = E;
        fn allocate_hash<CS: ConstraintSystem<E>>(
            &self,
            mut cs: CS,
            inputs: &[AllocatedNum<E>],
        ) -> CResult<AllocatedNum<E>> {
            use sapling_crypto::circuit::boolean::Boolean;
            use sapling_crypto::circuit::pedersen_hash::pedersen_hash;
            use sapling_crypto::pedersen_hash::Personalization;
            let mut bits: Vec<Boolean> = Vec::new();
            for (i, in_) in inputs.into_iter().enumerate() {
                bits.extend(in_.into_bits_le(cs.namespace(|| format!("bit split {}", i)))?);
            }
            Ok(pedersen_hash::<E, _>(
                cs.namespace(|| "hash"),
                Personalization::NoteCommitment,
                &bits,
                &self.params,
            )?
            .get_x()
            .clone())
        }
    }

    impl<E> CircuitHasher for BabyPedersen<E>
    where
        E: sapling_crypto::babyjubjub::JubjubEngine,
    {
        type E = E;
        fn allocate_hash<CS: ConstraintSystem<E>>(
            &self,
            mut cs: CS,
            inputs: &[AllocatedNum<E>],
        ) -> CResult<AllocatedNum<E>> {
            use sapling_crypto::baby_pedersen_hash::Personalization;
            use sapling_crypto::circuit::baby_pedersen_hash::pedersen_hash;
            use sapling_crypto::circuit::boolean::Boolean;
            let mut bits: Vec<Boolean> = Vec::new();
            for (i, in_) in inputs.into_iter().enumerate() {
                bits.extend(in_.into_bits_le(cs.namespace(|| format!("bit split {}", i)))?);
            }
            Ok(pedersen_hash::<E, _>(
                cs.namespace(|| "hash"),
                Personalization::NoteCommitment,
                &bits,
                &self.params,
            )?
            .get_x()
            .clone())
        }
    }

    impl<E> CircuitHasher for Mimc<E>
    where
        E: Engine
    {
        type E = E;
        fn allocate_hash<CS: ConstraintSystem<E>>(
            &self,
            cs: CS,
            inputs: &[AllocatedNum<E>],
        ) -> CResult<AllocatedNum<E>> {
            use hash::mimc;
            mimc::hash(cs, inputs)
        }
    }

    pub struct Bench<H: Hasher + CircuitHasher> {
        inputs: Vec<String>,
        hasher: H,
    }

    impl Bench<Poseidon<Bn256>> {
        pub fn poseidon_with_inputs(n_inputs: usize) -> Self {
            let p = Rc::new(Bn256PoseidonParams::new::<Keccak256Hasher>());
            Self {
                inputs: (0..n_inputs).map(|i| format!("{}", i)).collect(),
                hasher: Poseidon::<Bn256> { params: p.clone() },
            }
        }
    }

    impl Bench<Pedersen<Bn256>> {
        pub fn pedersen_with_inputs(n_inputs: usize) -> Self {
            let p = Rc::new(AltJubjubBn256::new());
            Self {
                inputs: (0..n_inputs).map(|i| format!("{}", i)).collect(),
                hasher: Pedersen::<Bn256> { params: p.clone() },
            }
        }
    }

    impl Bench<BabyPedersen<Bn256>> {
        pub fn baby_pedersen_with_inputs(n_inputs: usize) -> Self {
            let p = Rc::new(sapling_crypto::babyjubjub::JubjubBn256::new());
            Self {
                inputs: (0..n_inputs).map(|i| format!("{}", i)).collect(),
                hasher: BabyPedersen::<Bn256> { params: p.clone() },
            }
        }
    }

    impl Bench<Mimc<Bn256>> {
        pub fn mimc_with_inputs(n_inputs: usize) -> Self {
            Self {
                inputs: (0..n_inputs).map(|i| format!("{}", i)).collect(),
                hasher: Mimc::new(),
            }
        }
    }

    impl<E: Engine, H: Hasher<F = E::Fr> + CircuitHasher<E = E>> Circuit<E> for Bench<H> {
        fn synthesize<CS: ConstraintSystem<E>>(self, cs: &mut CS) -> CResult<()> {
            let inputs_values: Vec<E::Fr> = self
                .inputs
                .iter()
                .map(|i| E::Fr::from_str(i).unwrap())
                .collect();
            let inputs: Vec<AllocatedNum<E>> = inputs_values
                .iter()
                .enumerate()
                .map(|(i, v)| {
                    AllocatedNum::alloc(cs.namespace(|| format!("in {}", i)), || Ok(v.clone()))
                })
                .collect::<Result<Vec<_>, _>>()?;
            let expected_value = self.hasher.hash(&inputs_values);
            let expected = AllocatedNum::alloc(cs.namespace(|| "expected"), || Ok(expected_value))?;
            let actual = self
                .hasher
                .allocate_hash(cs.namespace(|| "hash"), &inputs)?;
            cs.enforce(
                || "eq",
                |lc| lc,
                |lc| lc,
                |lc| lc + expected.get_variable() - actual.get_variable(),
            );
            Ok(())
        }
    }

    #[cfg(test)]
    mod test {
        use super::Bench;
        use test_helpers::*;

        circuit_tests! {
            poseidon_2: (Bench::poseidon_with_inputs(2), true),
            poseidon_3: (Bench::poseidon_with_inputs(3), true),
            poseidon_4: (Bench::poseidon_with_inputs(4), true),
            poseidon_5: (Bench::poseidon_with_inputs(5), true),
            poseidon_6: (Bench::poseidon_with_inputs(6), true),
            poseidon_7: (Bench::poseidon_with_inputs(7), true),
            poseidon_8: (Bench::poseidon_with_inputs(8), true),
            poseidon_9: (Bench::poseidon_with_inputs(9), true),
            poseidon_10: (Bench::poseidon_with_inputs(10), true),
            poseidon_11: (Bench::poseidon_with_inputs(11), true),
            poseidon_12: (Bench::poseidon_with_inputs(12), true),
            poseidon_13: (Bench::poseidon_with_inputs(13), true),
            poseidon_14: (Bench::poseidon_with_inputs(14), true),
            poseidon_15: (Bench::poseidon_with_inputs(15), true),
            poseidon_16: (Bench::poseidon_with_inputs(16), true),

            pedersen_2: (Bench::pedersen_with_inputs(2), true),

            baby_pedersen_2: (Bench::baby_pedersen_with_inputs(2), true),

            mimc_2: (Bench::mimc_with_inputs(2), true),
            mimc_3: (Bench::mimc_with_inputs(3), true),
            mimc_4: (Bench::mimc_with_inputs(4), true),
            mimc_5: (Bench::mimc_with_inputs(5), true),
            mimc_6: (Bench::mimc_with_inputs(6), true),
            mimc_7: (Bench::mimc_with_inputs(7), true),
            mimc_8: (Bench::mimc_with_inputs(8), true),
            mimc_9: (Bench::mimc_with_inputs(9), true),
        }
    }
}
