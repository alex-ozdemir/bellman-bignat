use sapling_crypto::jubjub::JubjubEngine;
use sapling_crypto::babyjubjub::JubjubBn256;
use sapling_crypto::alt_babyjubjub::AltJubjubBn256;
use sapling_crypto::poseidon::{PoseidonEngine, PoseidonHashParams, QuinticSBox, bn256::Bn256PoseidonParams};
use sapling_crypto::bellman::pairing::bn256::Bn256;
use sapling_crypto::group_hash::Keccak256Hasher;
use sapling_crypto::bellman::pairing::Engine;
use sapling_crypto::bellman::ConstraintSystem;
use sapling_crypto::circuit::num::AllocatedNum;

use std::marker::PhantomData;
use std::rc::Rc;
use std::default::Default;

use super::circuit::CircuitHasher;
use super::Hasher;

use CResult;

pub mod mimc;

#[derive(Derivative)]
#[derivative(Clone(bound = ""))]
pub struct Poseidon<E>
where
    E: PoseidonEngine<SBox = QuinticSBox<E>>,
{
    pub params: Rc<E::Params>,
}

impl Default for Poseidon<Bn256>
{
    fn default() -> Self {
        Self {
            params: Rc::new(Bn256PoseidonParams::new::<Keccak256Hasher>()),
        }
    }
}

impl<E> Hasher for Poseidon<E>
where
    E: PoseidonEngine<SBox = QuinticSBox<E>>,
{
    type F = E::Fr;

    fn hash(&self, inputs: &[E::Fr]) -> E::Fr {
        use sapling_crypto::poseidon::poseidon_hash;
        assert_eq!(self.params.output_len(), 1);
        poseidon_hash::<E>(&self.params, inputs).pop().unwrap()
    }

    fn hash2(&self, a: Self::F, b: Self::F) -> Self::F {
        use sapling_crypto::poseidon::poseidon_hash;
        poseidon_hash::<E>(&self.params, &[a, b]).pop().unwrap()
    }
}

#[derive(Derivative)]
#[derivative(Clone(bound = ""))]
pub struct Pedersen<E>
where
    E: JubjubEngine,
{
    pub params: Rc<E::Params>,
}

impl<E: JubjubEngine> Hasher for Pedersen<E> {
    type F = E::Fr;
    fn hash2(&self, a: Self::F, b: Self::F) -> Self::F {
        use sapling_crypto::bellman::pairing::ff::PrimeField;
        use sapling_crypto::pedersen_hash::pedersen_hash;
        use sapling_crypto::pedersen_hash::Personalization;
        let mut bits: Vec<bool> = Vec::new();
        for i in &[a, b] {
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

impl Default for Pedersen<Bn256>
{
    fn default() -> Self {
        Self {
            params: Rc::new(AltJubjubBn256::new()),
        }
    }
}

#[derive(Derivative)]
#[derivative(Clone(bound = ""))]
pub struct BabyPedersen<E>
where
    E: sapling_crypto::babyjubjub::JubjubEngine,
{
    pub params: Rc<E::Params>,
}

impl<E: sapling_crypto::babyjubjub::JubjubEngine> Hasher for BabyPedersen<E> {
    type F = E::Fr;
    fn hash2(&self, a: Self::F, b: Self::F) -> Self::F {
        use sapling_crypto::baby_pedersen_hash::pedersen_hash;
        use sapling_crypto::baby_pedersen_hash::Personalization;
        use sapling_crypto::bellman::pairing::ff::PrimeField;
        let mut bits: Vec<bool> = Vec::new();
        for i in &[a, b] {
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

impl Default for BabyPedersen<Bn256>
{
    fn default() -> Self {
        Self {
            params: Rc::new(JubjubBn256::new()),
        }
    }
}

#[derive(Derivative)]
#[derivative(Clone(bound = ""))]
pub struct Mimc<E>
where
    E: Engine,
{
    _params: PhantomData<E>,
}

impl<E> Default for Mimc<E>
where
    E: Engine,
{
    fn default() -> Self {
        Self {
            _params: PhantomData::<E>::default(),
        }
    }
}

impl<E: Engine> Hasher for Mimc<E> {
    type F = E::Fr;
    fn hash2(&self, a: Self::F, b: Self::F) -> Self::F {
        mimc::helper::compression(a, b)
    }
}

impl<E> CircuitHasher for Poseidon<E>
where
    E: PoseidonEngine<SBox = QuinticSBox<E>>,
{
    type E = E;
    fn allocate_hash2<CS: ConstraintSystem<E>>(
        &self,
        cs: CS,
        a: &AllocatedNum<Self::E>,
        b: &AllocatedNum<Self::E>,
    ) -> CResult<AllocatedNum<E>> {
        use sapling_crypto::circuit::poseidon_hash::poseidon_hash;
        assert_eq!(self.params.output_len(), 1);
        Ok(
            poseidon_hash::<E, CS>(cs, &[a.clone(), b.clone()], &self.params)?
                .pop()
                .unwrap(),
        )
    }
    fn allocate_hash<CS: ConstraintSystem<E>>(
        &self,
        cs: CS,
        inputs: &[AllocatedNum<Self::E>],
    ) -> CResult<AllocatedNum<E>> {
        use sapling_crypto::circuit::poseidon_hash::poseidon_hash;
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
    fn allocate_hash2<CS: ConstraintSystem<E>>(
        &self,
        mut cs: CS,
        a: &AllocatedNum<Self::E>,
        b: &AllocatedNum<Self::E>,
    ) -> CResult<AllocatedNum<E>> {
        use sapling_crypto::circuit::boolean::Boolean;
        use sapling_crypto::circuit::pedersen_hash::pedersen_hash;
        use sapling_crypto::pedersen_hash::Personalization;
        let mut bits: Vec<Boolean> = Vec::new();
        for (i, in_) in [a, b].into_iter().enumerate() {
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
    fn allocate_hash2<CS: ConstraintSystem<E>>(
        &self,
        mut cs: CS,
        a: &AllocatedNum<Self::E>,
        b: &AllocatedNum<Self::E>,
    ) -> CResult<AllocatedNum<E>> {
        use sapling_crypto::baby_pedersen_hash::Personalization;
        use sapling_crypto::circuit::baby_pedersen_hash::pedersen_hash;
        use sapling_crypto::circuit::boolean::Boolean;
        let mut bits: Vec<Boolean> = Vec::new();
        for (i, in_) in [a, b].into_iter().enumerate() {
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
    E: Engine,
{
    type E = E;
    fn allocate_hash2<CS: ConstraintSystem<E>>(
        &self,
        mut cs: CS,
        a: &AllocatedNum<Self::E>,
        b: &AllocatedNum<Self::E>,
    ) -> CResult<AllocatedNum<E>> {
        let num = mimc::compression(cs.namespace(|| "hash"), a.clone(), b.clone())?;
        mimc::allocate_num(cs.namespace(|| "copy"), num)
    }
}
