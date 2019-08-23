use num::Num;
use sapling_crypto::bellman::pairing::ff::Field;
use sapling_crypto::bellman::{ConstraintSystem, SynthesisError};
use sapling_crypto::circuit::boolean::Boolean;
use sapling_crypto::circuit::num::AllocatedNum;
use sapling_crypto::poseidon::{PoseidonEngine, PoseidonHashParams, QuinticSBox};

use bignat::BigNat;
use usize_to_f;

pub mod helper {

    use num_bigint::BigUint;
    use num_traits::One;
    use sapling_crypto::poseidon::{
        poseidon_hash, PoseidonEngine, PoseidonHashParams, QuinticSBox,
    };
    use {f_to_nat, usize_to_f};

    pub fn hash_to_rsa_element<E: PoseidonEngine<SBox = QuinticSBox<E>>>(
        inputs: &[E::Fr],
        desired_bits: usize,
        params: &E::Params,
    ) -> BigUint {
        assert_eq!(params.output_len(), 1);
        assert_eq!(params.security_level(), 126);

        let bits_per_hash = params.security_level() as usize * 2;
        let bits_from_hash = desired_bits - 2;
        let n_hashes = (bits_from_hash - 1) / bits_per_hash + 1;

        // First we hash the inputs.
        let hash = poseidon_hash::<E>(params, inputs).pop().unwrap();

        // Then we add 4 different suffixes and hash each
        let hashes: BigUint = (0..n_hashes)
            .map(|i| {
                let elem = poseidon_hash::<E>(params, &[hash, usize_to_f(i)])
                    .pop()
                    .unwrap();
                let mut nat = f_to_nat(&elem) & ((BigUint::from(1usize) << bits_per_hash) - 1usize);
                nat <<= bits_per_hash * i;
                nat
            })
            .sum();

        // Now we assemble the 1024b number. Notice the ORs are all disjoint.
        let mut acc = BigUint::one();
        acc |= (hashes & ((BigUint::one() << bits_from_hash) - 1usize)) << 1;
        acc |= BigUint::one() << (desired_bits - 1);
        acc
    }
}

pub fn hash_to_rsa_element<E: PoseidonEngine<SBox = QuinticSBox<E>>, CS: ConstraintSystem<E>>(
    mut cs: CS,
    input: &[AllocatedNum<E>],
    limb_width: usize,
    desired_bits: usize,
    params: &E::Params,
) -> Result<BigNat<E>, SynthesisError> {
    if params.output_len() != 1 && params.security_level() != 126 {
        return Err(SynthesisError::Unsatisfiable);
    }
    let bits_per_hash = params.security_level() as usize * 2;
    let bits_from_hash = desired_bits - 2;
    let n_hashes = (bits_from_hash - 1) / bits_per_hash + 1;

    // First we hash the inputs
    let hash = sapling_crypto::circuit::poseidon_hash::poseidon_hash(
        cs.namespace(|| "inputs"),
        &input,
        params,
    )?
    .pop()
    .unwrap();

    // Now we hash the suffixes
    let hashes = (0..n_hashes)
        .map(|i| {
            let input = [
                hash.clone(),
                AllocatedNum::alloc(cs.namespace(|| format!("suffix {}", i)), || {
                    Ok(usize_to_f(i))
                })?,
            ];
            sapling_crypto::circuit::poseidon_hash::poseidon_hash(
                cs.namespace(|| format!("hash {}", i)),
                &input,
                &params,
                // Unwrap is safe b/c we know there is 1 output.
            )
            .map(|mut h| h.pop().unwrap())
        })
        .collect::<Result<Vec<_>, _>>()?;

    let bits: Vec<Boolean> = hashes
        .into_iter()
        .enumerate()
        .map(|(i, n)| {
            n.into_bits_le_strict(cs.namespace(|| format!("bitify {}", i)))
        })
        .collect::<Result<Vec<_>, _>>()?
        .into_iter()
        .flat_map(|mut v| {
            v.truncate(bits_per_hash);
            v
        })
        .collect();

    let mut all_bits = Vec::new();
    all_bits.push(Boolean::Constant(true));
    all_bits.extend(bits.into_iter().take(bits_from_hash));
    all_bits.push(Boolean::Constant(true));
    let nat = BigNat::from_limbs(
        all_bits
            .into_iter()
            .map(|bit| {
                let lc = bit.lc(CS::one(), E::Fr::one());
                let val = bit
                    .get_value()
                    .map(|v| if v { E::Fr::one() } else { E::Fr::zero() });
                Num::new(val, lc)
            })
            .collect(),
        1,
    );
    Ok(nat.group_limbs(limb_width))
}

#[cfg(test)]
mod test {
    use super::*;

    use OptionExt;

    use test_helpers::*;

    #[derive(Debug)]
    pub struct RsaHashInputs<'a> {
        pub inputs: &'a [&'a str],
    }

    #[derive(Debug)]
    pub struct RsaHashParams<E: PoseidonEngine<SBox = QuinticSBox<E>>> {
        pub desired_bits: usize,
        pub hash: E::Params,
    }

    pub struct RsaHash<'a, E: PoseidonEngine<SBox = QuinticSBox<E>>> {
        inputs: Option<RsaHashInputs<'a>>,
        params: RsaHashParams<E>,
    }

    impl<'a, E: PoseidonEngine<SBox = QuinticSBox<E>>> Circuit<E> for RsaHash<'a, E> {
        fn synthesize<CS: ConstraintSystem<E>>(self, cs: &mut CS) -> Result<(), SynthesisError> {
            let input_values: Vec<E::Fr> = self
                .inputs
                .grab()?
                .inputs
                .iter()
                .map(|s| E::Fr::from_str(s).unwrap())
                .collect();

            let expected_ouput = super::helper::hash_to_rsa_element::<E>(
                &input_values,
                self.params.desired_bits,
                &self.params.hash,
            );
            let allocated_expected_output =
                BigNat::alloc_from_nat(cs.namespace(|| "output"), || Ok(expected_ouput), 32, self.params.desired_bits / 32)?;
            let allocated_inputs: Vec<AllocatedNum<E>> = input_values
                .into_iter()
                .enumerate()
                .map(|(i, value)| {
                    AllocatedNum::alloc(cs.namespace(|| format!("input {}", i)), || Ok(value))
                })
                .collect::<Result<Vec<_>, _>>()?;
            let hash = super::hash_to_rsa_element(
                cs.namespace(|| "hash"),
                &allocated_inputs,
                32,
                self.params.desired_bits,
                &self.params.hash,
            )?;
            assert_eq!(hash.limbs.len() * hash.limb_width, self.params.desired_bits);
            hash.equal(cs.namespace(|| "eq"), &allocated_expected_output)?;
            Ok(())
        }
    }

    use sapling_crypto::group_hash::Keccak256Hasher;
    use sapling_crypto::poseidon::bn256::Bn256PoseidonParams;

    circuit_tests! {
        hash_one: (RsaHash {
            inputs: Some(
                RsaHashInputs {
                    inputs: &[
                        "1",
                    ],
                }
            ),
            params: RsaHashParams {
                desired_bits: 1024,
                hash: Bn256PoseidonParams::new::<Keccak256Hasher>(),
            }
        }, true),
        hash_ten: (RsaHash {
            inputs: Some(
                RsaHashInputs {
                    inputs: &[
                        "1", "2", "3", "4", "5", "6", "7", "8", "9", "10",
                    ],
                }
            ),
            params: RsaHashParams {
                desired_bits: 1024,
                hash: Bn256PoseidonParams::new::<Keccak256Hasher>(),
            }
        }, true),
        hash_ten_bit_flip: (RsaHash {
            inputs: Some(
                RsaHashInputs {
                    inputs: &[
                        "1", "2", "3", "4", "5", "6", "7", "8", "9", "9",
                    ],
                }
            ),
            params: RsaHashParams {
                desired_bits: 1024,
                hash: Bn256PoseidonParams::new::<Keccak256Hasher>(),
            }
        }, true),
        hash_ten_2048: (RsaHash {
            inputs: Some(
                RsaHashInputs {
                    inputs: &[
                        "1", "2", "3", "4", "5", "6", "7", "8", "9", "10",
                    ],
                }
            ),
            params: RsaHashParams {
                desired_bits: 2048,
                hash: Bn256PoseidonParams::new::<Keccak256Hasher>(),
            }
        }, true),
    }
}
