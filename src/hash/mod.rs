pub mod miller_rabin_prime;
pub mod pocklington;
pub mod rsa;

/// A representation of an integer domain to hash to
#[derive(Clone)]
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

pub mod helper {

    use num_bigint::BigUint;
    use num_traits::One;

    /// Given an integer, returns the integer with its low `k` bits.
    pub fn low_k_bits(n: &BigUint, k: usize) -> BigUint {
        n & ((BigUint::one() << k) - 1usize)
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use sapling_crypto::bellman::pairing::ff::{PrimeField};
    use sapling_crypto::bellman::{ConstraintSystem, SynthesisError};
    use sapling_crypto::circuit::num::AllocatedNum;
    use sapling_crypto::group_hash::Keccak256Hasher;
    use sapling_crypto::poseidon::bn256::Bn256PoseidonParams;
    use sapling_crypto::poseidon::{PoseidonEngine, QuinticSBox};

    use bignat::BigNat;
    use sapling_crypto::bellman::pairing::ff::ScalarEngine;
    use OptionExt;

    use test_helpers::*;

    #[test]
    fn pocklington_plan_128() {
        assert_eq!(
            vec![31, 62, 9],
            pocklington::helper::PocklingtonPlan::new(128).extensions
        );
    }

    //#[test]
    //fn pocklington_extension_0() {
    //    let cert = Base(BigUint::from(241usize));
    //    let extension = BigUint::from(6usize);
    //    let ex = Ok(Recursive {
    //        rec: Box::new(cert.clone()),
    //        number: BigUint::from(1447usize),
    //        base: BigUint::from(2usize),
    //        extension: extension.clone(),
    //        nonce: 0,
    //    });
    //    let act = helper::attempt_pocklington_extension::<<Bn256 as ScalarEngine>::Fr>(cert, extension);
    //    assert_eq!(ex, act);
    //}

    macro_rules! pocklington_hash_tests {
        ($($name:ident: $value:expr,)*) => {
            $(
                #[test]
                fn $name() {
                    let (inputs, entropy) = $value;
                    let input_values: Vec<<Bn256 as ScalarEngine>::Fr> = inputs
                        .iter()
                        .map(|s| <Bn256 as ScalarEngine>::Fr::from_str(s).unwrap())
                        .collect();
                    let params = Bn256PoseidonParams::new::<Keccak256Hasher>();
                    let cert = pocklington::helper::hash_to_pocklington_prime::<Bn256>(&input_values, entropy, &params).expect("pocklington generation failed");
                    assert!(crate::hash::miller_rabin_prime::helper::miller_rabin(cert.number(), 20));
                }
            )*
        }
    }

    pocklington_hash_tests! {
        pocklington_hash_helper_128_1: (&["1"], 128),
        pocklington_hash_helper_128_2: (&["2"], 128),
        pocklington_hash_helper_128_3: (&["3"], 128),
        pocklington_hash_helper_128_4: (&["4"], 128),
    }

    #[derive(Debug)]
    pub struct PockHashInputs<'a> {
        pub inputs: &'a [&'a str],
    }

    #[derive(Debug)]
    pub struct PockHashParams<E: PoseidonEngine<SBox = QuinticSBox<E>>> {
        pub entropy: usize,
        pub hash: E::Params,
    }

    pub struct PockHash<'a, E: PoseidonEngine<SBox = QuinticSBox<E>>> {
        inputs: Option<PockHashInputs<'a>>,
        params: PockHashParams<E>,
    }

    impl<'a, E: PoseidonEngine<SBox = QuinticSBox<E>>> Circuit<E> for PockHash<'a, E> {
        fn synthesize<CS: ConstraintSystem<E>>(self, cs: &mut CS) -> Result<(), SynthesisError> {
            let input_values: Vec<E::Fr> = self
                .inputs
                .grab()?
                .inputs
                .iter()
                .map(|s| E::Fr::from_str(s).unwrap())
                .collect();
            let cert = super::pocklington::helper::hash_to_pocklington_prime::<E>(
                &input_values,
                self.params.entropy,
                &self.params.hash,
            )
            .expect("pocklington hash failed");
            let plan = super::pocklington::helper::PocklingtonPlan::new(self.params.entropy);
            let allocated_expected_output = BigNat::alloc_from_nat(
                cs.namespace(|| "output"),
                || Ok(cert.number().clone()),
                32,
                (plan.max_bits() - 1) / 32 + 1,
            )?;
            let allocated_inputs: Vec<AllocatedNum<E>> = input_values
                .into_iter()
                .enumerate()
                .map(|(i, value)| {
                    AllocatedNum::alloc(cs.namespace(|| format!("input {}", i)), || Ok(value))
                })
                .collect::<Result<Vec<_>, _>>()?;
            let hash = super::pocklington::hash_to_pocklington_prime(
                cs.namespace(|| "hash"),
                &allocated_inputs,
                32,
                self.params.entropy,
                &self.params.hash,
            )?;
            hash.equal(cs.namespace(|| "eq"), &allocated_expected_output)?;
            Ok(())
        }
    }

    circuit_tests! {
        pocklington_hash_29_1: (
            PockHash {
                inputs: Some(PockHashInputs {
                    inputs: &["1","2","3","4","5","6","7","8","9","10"],
                }),
                params: PockHashParams {
                    entropy: 29,
                    hash: Bn256PoseidonParams::new::<Keccak256Hasher>(),
                },
            },
            true,
        ),
        pocklington_hash_30_1: (
            PockHash {
                inputs: Some(PockHashInputs {
                    inputs: &["1","2","3","4","5","6","7","8","9","10"],
                }),
                params: PockHashParams {
                    entropy: 30,
                    hash: Bn256PoseidonParams::new::<Keccak256Hasher>(),
                },
            },
            true,
        ),
        pocklington_hash_50_1: (
            PockHash {
                inputs: Some(PockHashInputs {
                    inputs: &["1","2","3","4","5","6","7","8","9","10"],
                }),
                params: PockHashParams {
                    entropy: 50,
                    hash: Bn256PoseidonParams::new::<Keccak256Hasher>(),
                },
            },
            true,
        ),
        pocklington_hash_80_1: (
            PockHash {
                inputs: Some(PockHashInputs {
                    inputs: &["1","2","3","4","5","6","7","8","9","10"],
                }),
                params: PockHashParams {
                    entropy: 80,
                    hash: Bn256PoseidonParams::new::<Keccak256Hasher>(),
                },
            },
            true,
        ),
        pocklington_hash_128_1: (
            PockHash {
                inputs: Some(PockHashInputs {
                    inputs: &["1","2","3","4","5","6","7","8","9","10"],
                }),
                params: PockHashParams {
                    entropy: 128,
                    hash: Bn256PoseidonParams::new::<Keccak256Hasher>(),
                },
            },
            true,
        ),
        pocklington_hash_160_1: (
            PockHash {
                inputs: Some(PockHashInputs {
                    inputs: &["1","2","3","4","5","6","7","8","9","10"],
                }),
                params: PockHashParams {
                    entropy: 160,
                    hash: Bn256PoseidonParams::new::<Keccak256Hasher>(),
                },
            },
            true,
        ),
    }
}
