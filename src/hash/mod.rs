pub mod miller_rabin_prime;
pub mod pocklington;
pub mod rsa;
pub mod hashes;

use std::clone::Clone;

use num_bigint::BigUint;
use num_traits::One;
use sapling_crypto::bellman::pairing::ff::PrimeField;
use sapling_crypto::bellman::pairing::ff::Field;

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
    use sapling_crypto::bellman::pairing::bn256::Bn256;
    use sapling_crypto::bellman::pairing::ff::Field;
    use sapling_crypto::bellman::pairing::ff::PrimeField;
    use sapling_crypto::bellman::pairing::ff::ScalarEngine;
    use sapling_crypto::bellman::pairing::Engine;
    use sapling_crypto::bellman::{Circuit, ConstraintSystem};
    use sapling_crypto::circuit::num::AllocatedNum;
    use sapling_crypto::group_hash::Keccak256Hasher;
    use sapling_crypto::poseidon::bn256::Bn256PoseidonParams;
    use sapling_crypto::alt_babyjubjub::AltJubjubBn256;

    use std::clone::Clone;
    use std::rc::Rc;

    use super::Hasher;
    use CResult;
    use super::hashes::{Poseidon, Pedersen, BabyPedersen, Mimc};

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
