pub mod division_intractable;
pub mod hashes;
pub mod integer;
pub mod miller_rabin_prime;
pub mod pocklington;

use std::clone::Clone;

use num_bigint::BigUint;
use num_traits::One;
use sapling_crypto::bellman::pairing::ff::Field;
use sapling_crypto::bellman::pairing::ff::PrimeField;

/// A representation of an integer domain to hash to
#[derive(Clone, Debug)]
pub struct HashDomain {
    pub n_bits: usize,
    pub n_trailing_ones: usize,
}

impl HashDomain {
    pub fn nonce_width(&self) -> usize {
        let n_rounds = -128f64 * 2f64.ln() / (1f64 - 2f64 / self.n_bits as f64).ln();
        let n_bits = (n_rounds.log2().ceil() + 0.1) as usize;
        n_bits
    }
}

/// Given an integer, returns the integer with its low `k` bits.
pub fn low_k_bits(n: &BigUint, k: usize) -> BigUint {
    n & ((BigUint::one() << k) - 1usize)
}

pub trait Hasher: Clone {
    type F: PrimeField;
    fn hash2(&self, a: Self::F, b: Self::F) -> Self::F;
    fn hash(&self, inputs: &[Self::F]) -> Self::F {
        let mut acc = Self::F::zero();
        for input in inputs {
            acc = self.hash2(acc, input.clone());
        }
        acc
    }
}

pub mod circuit {
    use sapling_crypto::bellman::pairing::ff::Field;
    use sapling_crypto::bellman::pairing::ff::PrimeField;
    use sapling_crypto::bellman::pairing::ff::ScalarEngine;
    use sapling_crypto::bellman::pairing::Engine;
    use sapling_crypto::bellman::{Circuit, ConstraintSystem};
    use sapling_crypto::circuit::num::AllocatedNum;

    use std::clone::Clone;

    use super::Hasher;
    use CResult;

    #[derive(Derivative)]
    #[derivative(Clone(bound = ""))]
    pub struct MaybeHashed<E: Engine> {
        pub values: Vec<AllocatedNum<E>>,
        pub hash: Option<AllocatedNum<E>>,
    }

    impl<E: Engine> MaybeHashed<E> {
        pub fn new(values: Vec<AllocatedNum<E>>, hash: AllocatedNum<E>) -> Self {
            Self {
                values,
                hash: Some(hash),
            }
        }
        pub fn from_values(values: Vec<AllocatedNum<E>>) -> Self {
            Self { values, hash: None }
        }
        pub fn get_hash<F: FnOnce(&[AllocatedNum<E>]) -> CResult<AllocatedNum<E>>>(
            &mut self,
            f: F,
        ) -> CResult<AllocatedNum<E>> {
            if self.hash.is_none() {
                self.hash = Some(f(&self.values)?);
            }
            Ok(self.hash.clone().unwrap())
        }
    }

    pub trait CircuitHasher: Clone {
        type E: Engine;
        fn allocate_hash2<CS: ConstraintSystem<Self::E>>(
            &self,
            cs: CS,
            a: &AllocatedNum<Self::E>,
            b: &AllocatedNum<Self::E>,
        ) -> CResult<AllocatedNum<Self::E>>;

        fn allocate_hash<CS: ConstraintSystem<Self::E>>(
            &self,
            mut cs: CS,
            inputs: &[AllocatedNum<Self::E>],
        ) -> CResult<AllocatedNum<Self::E>> {
            let mut acc = AllocatedNum::alloc(cs.namespace(|| "zero"), || {
                Ok(<<Self::E as ScalarEngine>::Fr as Field>::zero())
            })?;
            for (i, input) in inputs.into_iter().enumerate() {
                acc = self.allocate_hash2(cs.namespace(|| format!("chain {}", i)), &acc, input)?;
            }
            Ok(acc)
        }
    }

    #[derive(Clone)]
    pub struct Bench<H: Hasher + CircuitHasher> {
        inputs: Vec<String>,
        hasher: H,
    }

    impl<H: Hasher + CircuitHasher> Bench<H> {
        pub fn from_hasher(hasher: H, n_inputs: usize) -> Self {
            Self {
                inputs: (0..n_inputs).map(|i| format!("{}", i)).collect(),
                hasher,
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
        use hash::hashes::{Mimc, Pedersen, Poseidon, Sha256};
        use sapling_crypto::bellman::pairing::bn256::Bn256;
        use util::test_helpers::*;

        circuit_tests! {
                    bn256_poseidon_2: (Bench::from_hasher(Poseidon::<Bn256>::default(), 2), true),
                    bn256_poseidon_5: (Bench::from_hasher(Poseidon::<Bn256>::default(), 5), true),
                    bn256_poseidon_10: (Bench::from_hasher(Poseidon::<Bn256>::default(), 10), true),

                    bn256_pedersen_2: (Bench::from_hasher(Pedersen::<Bn256>::default(), 2), true),
                    bn256_pedersen_5: (Bench::from_hasher(Pedersen::<Bn256>::default(), 5), true),
                    bn256_pedersen_10: (Bench::from_hasher(Pedersen::<Bn256>::default(), 10), true),

                    bn256_sha_2: (Bench::from_hasher(Sha256::default(), 2), true),
                    bn256_sha_5: (Bench::from_hasher(Sha256::default(), 5), true),

                    bn256_mimc_2: (Bench::from_hasher(Mimc::default(), 2), true),
                    bn256_mimc_5: (Bench::from_hasher(Mimc::default(), 5), true),

        //            bls12_poseidon_2: (Bench::from_hasher(Poseidon::<Bls12>::default(), 2), true),
        //            bls12_poseidon_5: (Bench::from_hasher(Poseidon::<Bls12>::default(), 5), true),
        //            bls12_poseidon_10: (Bench::from_hasher(Poseidon::<Bls12>::default(), 10), true),
        //
        //            bls12_pedersen_2: (Bench::from_hasher(Pedersen::<Bls12>::default(), 2), true),
        //            bls12_pedersen_5: (Bench::from_hasher(Pedersen::<Bls12>::default(), 5), true),
        //            bls12_pedersen_10: (Bench::from_hasher(Pedersen::<Bls12>::default(), 10), true),
        //
        //            bls12_sha_2: (Bench::from_hasher(Sha256::default(), 2), true),
        //            bls12_sha_5: (Bench::from_hasher(Sha256::default(), 5), true),
        //
        //            bls12_mimc_2: (Bench::from_hasher(Mimc::default(), 2), true),
        //            bls12_mimc_5: (Bench::from_hasher(Mimc::default(), 5), true),
                }
    }
}
