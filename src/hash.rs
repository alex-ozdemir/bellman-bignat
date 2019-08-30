use num::Num;
use sapling_crypto::bellman::pairing::ff::Field;
use sapling_crypto::bellman::{ConstraintSystem, LinearCombination, SynthesisError};
use sapling_crypto::circuit::boolean::Boolean;
use sapling_crypto::circuit::num::AllocatedNum;
use sapling_crypto::poseidon::{PoseidonEngine, PoseidonHashParams, QuinticSBox};

use num_bigint::BigUint;

use bignat::BigNat;
use usize_to_f;
use OptionExt;

const MILLER_RABIN_ROUNDS: usize = 2;

/// A representation of the hash of
pub struct HashDomain {
    pub n_bits: usize,
    pub n_trailing_ones: usize,
}

/// Returns whether `n` passes Miller-Rabin checks with the first `rounds` primes as bases
fn miller_rabin(n: &BigUint, rounds: usize) -> bool {
    fn primes(n: usize) -> Vec<usize> {
        let mut ps = vec![2];
        let mut next = 3;
        while ps.len() < n {
            if !ps.iter().any(|p| next % p == 0) {
                ps.push(next);
            }
            next += 1;
        }
        ps
    }
    let ps = primes(rounds);
    !ps.into_iter()
        .any(|p| !miller_rabin_round(n, &BigUint::from(p)))
}

/// Returns whether `n` passes a Miller-Rabin check with base `b`.
fn miller_rabin_round(n: &BigUint, b: &BigUint) -> bool {
    let n_less_one = n - 1usize;
    let d = n - 1usize;
    let d_bits = d.to_str_radix(2);
    let last_one = d_bits.as_str().rfind('1').expect("Input must be >1");
    if last_one == d_bits.len() - 1 {
        return false;
    }
    let s = d_bits.len() - last_one - 1;
    let d = d >> s;
    let mut pow = b.modpow(&d, &n);
    if pow == BigUint::from(1usize) || pow == n_less_one {
        return true;
    }
    for _ in 0..(s - 1) {
        pow = &pow * &pow % n;
        if pow == n_less_one {
            return true;
        }
    }
    return false;
}

pub mod helper {

    use super::HashDomain;
    use num_bigint::BigUint;
    use num_traits::One;
    use sapling_crypto::bellman::pairing::ff::Field;
    use sapling_crypto::poseidon::{
        poseidon_hash, PoseidonEngine, PoseidonHashParams, QuinticSBox,
    };
    use {f_to_nat, usize_to_f};

    pub fn hash_to_rsa_element<E: PoseidonEngine<SBox = QuinticSBox<E>>>(
        inputs: &[E::Fr],
        domain: &HashDomain,
        params: &E::Params,
    ) -> BigUint {
        assert_eq!(params.output_len(), 1);
        assert_eq!(params.security_level(), 126);

        let bits_per_hash = params.security_level() as usize * 2;
        let bits_from_hash = domain.n_bits - 1 - domain.n_trailing_ones;
        let n_hashes = (bits_from_hash - 1) / bits_per_hash + 1;

        // First we hash the inputs.
        let hash = poseidon_hash::<E>(params, inputs).pop().unwrap();

        // Then we add 4 different suffixes and hash each
        let hashes: BigUint = if n_hashes > 1 {
            (0..n_hashes)
            .map(|i| {
                let elem = poseidon_hash::<E>(params, &[hash, usize_to_f(i)])
                    .pop()
                    .unwrap();
                let mut nat = f_to_nat(&elem) & ((BigUint::from(1usize) << bits_per_hash) - 1usize);
                nat <<= bits_per_hash * i;
                nat
            })
            .sum()
        } else {
            f_to_nat(&hash) & ((BigUint::from(1usize) << bits_per_hash) - 1usize)
        };

        // Now we assemble the 1024b number. Notice the ORs are all disjoint.
        let mut acc = (BigUint::one() << domain.n_trailing_ones) - 1usize;
        acc |= (hashes & ((BigUint::one() << bits_from_hash) - 1usize)) << domain.n_trailing_ones;
        acc |= BigUint::one() << (domain.n_bits - 1);
        acc
    }

    pub fn nonce_width(domain: &HashDomain) -> usize {
        let n_rounds = -128f64 * 2f64.ln() / (1f64 - 2f64 / domain.n_bits as f64).ln();
        let n_bits = (n_rounds.log2().ceil() + 0.1) as usize;
        n_bits
    }

    /// Given hash inputs, and a target domain for the prime hash, computes:
    ///
    ///    * an appropriate bitwidth for a nonce such that there exists a nonce appendable to the
    ///    inputs which will result in a prime hash with probability at least 1 - 2 ** -128
    ///    * the first such nonce in the range defined by the bitwidth
    ///    * the prime hash
    ///
    /// and returns a tupe `(hash, nonce, bitwidth)`.
    ///
    /// If, by misfortune, there is no such nonce, returns `None`.
    pub fn hash_to_prime<E: PoseidonEngine<SBox = QuinticSBox<E>>>(
        inputs: &[E::Fr],
        domain: &HashDomain,
        params: &E::Params,
    ) -> Option<(BigUint, E::Fr, usize)> {
        let n_bits = nonce_width(domain);
        let mut inputs: Vec<E::Fr> = inputs.iter().copied().collect();
        inputs.push(E::Fr::zero());
        for _ in 0..(1 << n_bits) {
            let hash = hash_to_rsa_element::<E>(&inputs, domain, params);
            if super::miller_rabin(&hash, 30) {
                // unwrap is safe because of the push above
                return Some((hash, inputs.pop().unwrap(), n_bits));
            }
            // unwrap is safe because of the push above
            inputs.last_mut().unwrap().add_assign(&E::Fr::one());
        }
        None
    }
}

pub fn hash_to_rsa_element<E: PoseidonEngine<SBox = QuinticSBox<E>>, CS: ConstraintSystem<E>>(
    mut cs: CS,
    input: &[AllocatedNum<E>],
    limb_width: usize,
    domain: &HashDomain,
    params: &E::Params,
) -> Result<BigNat<E>, SynthesisError> {
    if params.output_len() != 1 && params.security_level() != 126 {
        return Err(SynthesisError::Unsatisfiable);
    }
    let bits_per_hash = params.security_level() as usize * 2;
    let bits_from_hash = domain.n_bits - 1 - domain.n_trailing_ones;
    let n_hashes = (bits_from_hash - 1) / bits_per_hash + 1;

    // First we hash the inputs
    let hash = sapling_crypto::circuit::poseidon_hash::poseidon_hash(
        cs.namespace(|| "inputs"),
        &input,
        params,
    )?
    .pop()
    .unwrap();

    let bits: Vec<Boolean> = if n_hashes > 1 {
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

        hashes
            .into_iter()
            .enumerate()
            .map(|(i, n)| n.into_bits_le_strict(cs.namespace(|| format!("bitify {}", i))))
            .collect::<Result<Vec<_>, _>>()?
            .into_iter()
            .flat_map(|mut v| {
                v.truncate(bits_per_hash);
                v
            })
            .collect()
    } else {
        hash.into_bits_le_strict(cs.namespace(|| "bitify"))?
    };

    let mut all_bits = Vec::new();
    all_bits.extend(std::iter::repeat(Boolean::Constant(true)).take(domain.n_trailing_ones));
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

pub fn hash_to_prime<E: PoseidonEngine<SBox = QuinticSBox<E>>, CS: ConstraintSystem<E>>(
    mut cs: CS,
    input: &[AllocatedNum<E>],
    limb_width: usize,
    domain: &HashDomain,
    params: &E::Params,
) -> Result<BigNat<E>, SynthesisError> {
    if domain.n_trailing_ones < 2 {
        return Err(SynthesisError::Unsatisfiable);
    }
    let mut inputs: Vec<_> = input.iter().cloned().collect();
    let nonce = AllocatedNum::alloc(cs.namespace(|| "nonce"), || {
        let inputs = inputs
            .iter()
            .map(|i| i.get_value())
            .collect::<Option<Vec<E::Fr>>>();
        let (_, nonce, _) = helper::hash_to_prime::<E>(&inputs.grab()?, domain, params)
            .ok_or(SynthesisError::Unsatisfiable)?;
        Ok(nonce)
    })?;
    Num::new(
        nonce.get_value(),
        LinearCombination::zero() + nonce.get_variable(),
    )
    .fits_in_bits(cs.namespace(|| "nonce bound"), helper::nonce_width(domain))?;
    inputs.push(nonce);
    let hash = hash_to_rsa_element(cs.namespace(|| "hash"), &inputs, limb_width, domain, params)?;
    let res = hash.miller_rabin(cs.namespace(|| "primeck"), MILLER_RABIN_ROUNDS)?;
    Boolean::enforce_equal(cs.namespace(|| "result"), &Boolean::constant(true), &res)?;
    Ok(hash)
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
                &HashDomain {
                    n_bits: self.params.desired_bits,
                    n_trailing_ones: 1,
                },
                &self.params.hash,
            );
            let allocated_expected_output = BigNat::alloc_from_nat(
                cs.namespace(|| "output"),
                || Ok(expected_ouput),
                32,
                self.params.desired_bits / 32,
            )?;
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
                &HashDomain {
                    n_bits: self.params.desired_bits,
                    n_trailing_ones: 1,
                },
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

    #[test]
    fn mr_11() {
        assert_eq!(miller_rabin(&BigUint::from(11usize), 3), true);
    }

    #[test]
    fn mr_12() {
        assert_eq!(miller_rabin(&BigUint::from(12usize), 3), false);
    }

    #[test]
    fn mr_251() {
        assert_eq!(miller_rabin(&BigUint::from(251usize), 11), true);
    }

    #[test]
    fn mr_15() {
        assert_eq!(miller_rabin(&BigUint::from(15usize), 3), false);
    }

    #[derive(Debug)]
    pub struct PrimeHashInputs<'a> {
        pub inputs: &'a [&'a str],
    }

    #[derive(Debug)]
    pub struct PrimeHashParams<E: PoseidonEngine<SBox = QuinticSBox<E>>> {
        pub desired_bits: usize,
        pub hash: E::Params,
    }

    pub struct PrimeHash<'a, E: PoseidonEngine<SBox = QuinticSBox<E>>> {
        inputs: Option<PrimeHashInputs<'a>>,
        params: PrimeHashParams<E>,
    }

    impl<'a, E: PoseidonEngine<SBox = QuinticSBox<E>>> Circuit<E> for PrimeHash<'a, E> {
        fn synthesize<CS: ConstraintSystem<E>>(self, cs: &mut CS) -> Result<(), SynthesisError> {
            let input_values: Vec<E::Fr> = self
                .inputs
                .grab()?
                .inputs
                .iter()
                .map(|s| E::Fr::from_str(s).unwrap())
                .collect();
            let domain = HashDomain {
                n_bits: self.params.desired_bits,
                n_trailing_ones: 2,
            };
            let (expected_ouput, _, _) =
                super::helper::hash_to_prime::<E>(&input_values, &domain, &self.params.hash)
                    .unwrap();
            let allocated_expected_output = BigNat::alloc_from_nat(
                cs.namespace(|| "output"),
                || Ok(expected_ouput),
                32,
                self.params.desired_bits / 32,
            )?;
            let allocated_inputs: Vec<AllocatedNum<E>> = input_values
                .into_iter()
                .enumerate()
                .map(|(i, value)| {
                    AllocatedNum::alloc(cs.namespace(|| format!("input {}", i)), || Ok(value))
                })
                .collect::<Result<Vec<_>, _>>()?;
            let hash = super::hash_to_prime(
                cs.namespace(|| "hash"),
                &allocated_inputs,
                32,
                &domain,
                &self.params.hash,
            )?;
            assert_eq!(hash.limbs.len() * hash.limb_width, self.params.desired_bits);
            hash.equal(cs.namespace(|| "eq"), &allocated_expected_output)?;
            Ok(())
        }
    }

    circuit_tests! {
        prime_hash_one: (PrimeHash {
            inputs: Some(
                        PrimeHashInputs {
                            inputs: &[
                                "1",
                            ],
                        }
                    ),
                    params: PrimeHashParams {
                        desired_bits: 128,
                        hash: Bn256PoseidonParams::new::<Keccak256Hasher>(),
                    }
        }, true),
        prime_hash_ten: (PrimeHash {
            inputs: Some(
                        PrimeHashInputs {
                            inputs: &[
                                "0",
                                "1",
                                "2",
                                "3",
                                "5",
                                "6",
                                "7",
                                "8",
                                "9",
                            ],
                        }
                    ),
                    params: PrimeHashParams {
                        desired_bits: 128,
                        hash: Bn256PoseidonParams::new::<Keccak256Hasher>(),
                    }
        }, true),
    }
}
