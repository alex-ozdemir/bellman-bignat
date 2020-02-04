use sapling_crypto::alt_babyjubjub::AltJubjubBn256;
use sapling_crypto::bellman::pairing::bls12_381::Bls12;
use sapling_crypto::bellman::pairing::bn256::Bn256;
use sapling_crypto::bellman::pairing::Engine;
use sapling_crypto::bellman::ConstraintSystem;
use sapling_crypto::circuit::num::AllocatedNum;
use sapling_crypto::group_hash::Keccak256Hasher;
use sapling_crypto::jubjub::{JubjubBls12, JubjubEngine};
use sapling_crypto::poseidon::{
    bls12::Bls12PoseidonParams, bn256::Bn256PoseidonParams, PoseidonEngine, PoseidonHashParams,
    QuinticSBox,
};

use std::default::Default;
use std::marker::PhantomData;
use std::rc::Rc;

use super::circuit::CircuitHasher;
use super::Hasher;

use CResult;

pub mod mimc;
mod sha;

#[derive(Derivative)]
#[derivative(Clone(bound = ""))]
pub struct Poseidon<E>
where
    E: PoseidonEngine<SBox = QuinticSBox<E>>,
{
    pub params: Rc<E::Params>,
}

impl<E: PoseidonEngine<SBox = QuinticSBox<E>>> Poseidon<E> {
    fn from_params(p: E::Params) -> Self {
        Self { params: Rc::new(p) }
    }
}

impl Default for Poseidon<Bn256> {
    fn default() -> Self {
        Poseidon::from_params(Bn256PoseidonParams::new::<Keccak256Hasher>())
    }
}

impl Default for Poseidon<Bls12> {
    fn default() -> Self {
        Poseidon::from_params(Bls12PoseidonParams::new::<Keccak256Hasher>())
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
impl<E: JubjubEngine>  Pedersen<E> {
    fn from_params(p: E::Params) -> Self {
        Self {
            params: Rc::new(p),
        }
    }
}

impl Default for Pedersen<Bn256> {
    fn default() -> Self {
        Pedersen::from_params(AltJubjubBn256::new())
    }
}

impl Default for Pedersen<Bls12> {
    fn default() -> Self {
        Pedersen::from_params(JubjubBls12::new())
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

#[derive(Derivative)]
#[derivative(Clone(bound = ""))]
pub struct Sha256<E>
where
    E: Engine,
{
    _params: PhantomData<E>,
}

impl<E> Default for Sha256<E>
where
    E: Engine,
{
    fn default() -> Self {
        Self {
            _params: PhantomData::<E>::default(),
        }
    }
}

impl<E: Engine> Hasher for Sha256<E> {
    type F = E::Fr;
    fn hash2(&self, a: Self::F, b: Self::F) -> Self::F {
        sha::sha256::<E>(&[a, b])
    }
    fn hash(&self, inputs: &[E::Fr]) -> E::Fr {
        sha::sha256::<E>(inputs)
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

impl<E> CircuitHasher for Sha256<E>
where
    E: Engine,
{
    type E = E;
    fn allocate_hash2<CS: ConstraintSystem<E>>(
        &self,
        cs: CS,
        a: &AllocatedNum<Self::E>,
        b: &AllocatedNum<Self::E>,
    ) -> CResult<AllocatedNum<E>> {
        sha::circuit::sha256(cs, &[a.clone(), b.clone()])
    }
    fn allocate_hash<CS: ConstraintSystem<E>>(
        &self,
        cs: CS,
        inputs: &[AllocatedNum<Self::E>],
    ) -> CResult<AllocatedNum<E>> {
        sha::circuit::sha256(cs, inputs)
    }
}

#[cfg(test)]
mod tests {
    use test::Bencher;
    use super::*;
    use sapling_crypto::bellman::pairing::ff::Field;
    use util::test_helpers::*;
    use hash::circuit::Bench;

    fn bench_hasher_hash_n<H: Hasher>(h: H, n: usize, b: &mut Bencher) {
        let v = vec![H::F::one(); n];
        let zero = H::F::zero();
        b.iter(|| assert_ne!(zero, h.hash(&v)));
    }

    fn bench_hasher_hash2<H: Hasher>(h: H, b: &mut Bencher) {
        let i0 = H::F::one();
        let i1 = H::F::one();
        let zero = H::F::zero();
        b.iter(|| assert_ne!(zero, h.hash2(i0, i1)));
    }

    #[bench]
    fn poseidon_2_bench_bls12(b: &mut Bencher) {
        let h = Poseidon::<Bls12>::default();
        bench_hasher_hash2(h, b);
    }

    #[bench]
    fn pedersen_2_bench_bls12(b: &mut Bencher) {
        let h = Pedersen::<Bls12>::default();
        bench_hasher_hash2(h, b);
    }

    #[bench]
    fn mimc_2_bench_bls12(b: &mut Bencher) {
        let h = Mimc::<Bls12>::default();
        bench_hasher_hash2(h, b);
    }

    #[bench]
    fn sha_2_bench_bls12(b: &mut Bencher) {
        let h = Sha256::<Bls12>::default();
        bench_hasher_hash2(h, b);
    }

    #[bench]
    fn poseidon_5_bench_bls12(b: &mut Bencher) {
        let h = Poseidon::<Bls12>::default();
        bench_hasher_hash_n(h, 5, b);
    }

    circuit_benches! {
        bench_bn256_poseidon_2: (Bench::from_hasher(Poseidon::<Bls12>::default(), 2), true),

        bench_bn256_pedersen_2: (Bench::from_hasher(Pedersen::<Bls12>::default(), 2), true),

        bench_bn256_sha_2: (Bench::from_hasher(Sha256::<Bls12>::default(), 2), true),

        bench_bn256_mimc_2: (Bench::from_hasher(Mimc::<Bls12>::default(), 2), true),
    }

}
