use sapling_crypto::bellman::{ConstraintSystem, LinearCombination, SynthesisError};
use sapling_crypto::circuit::boolean::Boolean;
use sapling_crypto::circuit::num::AllocatedNum;
use sapling_crypto::poseidon::{PoseidonEngine, QuinticSBox};

use bignat::BigNat;
use hash::rsa::hash_to_integer;
use hash::HashDomain;
use num::Num;
use OptionExt;

const MILLER_RABIN_ROUNDS: usize = 3;

pub mod helper {
    use hash::rsa::helper::hash_to_integer;
    use hash::HashDomain;
    use num_bigint::BigUint;
    use sapling_crypto::bellman::pairing::ff::Field;
    use sapling_crypto::poseidon::{PoseidonEngine, QuinticSBox};

    /// Returns whether `n` passes Miller-Rabin checks with the first `rounds` primes as bases
    pub fn miller_rabin(n: &BigUint, rounds: usize) -> bool {
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

    pub fn miller_rabin_32b(n: &BigUint) -> bool {
        miller_rabin_round(n, &BigUint::from(2usize))
            && miller_rabin_round(n, &BigUint::from(7usize))
            && miller_rabin_round(n, &BigUint::from(61usize))
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
        let n_bits = domain.nonce_width();
        let mut inputs: Vec<E::Fr> = inputs.iter().copied().collect();
        inputs.push(E::Fr::zero());
        for _ in 0..(1 << n_bits) {
            let hash = hash_to_integer::<E>(&inputs, domain, params);
            if miller_rabin(&hash, 30) {
                // unwrap is safe because of the push above
                return Some((hash, inputs.pop().unwrap(), n_bits));
            }
            // unwrap is safe because of the push above
            inputs.last_mut().unwrap().add_assign(&E::Fr::one());
        }
        None
    }
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
    .fits_in_bits(cs.namespace(|| "nonce bound"), domain.nonce_width())?;
    inputs.push(nonce);
    let hash = hash_to_integer(cs.namespace(|| "hash"), &inputs, limb_width, domain, params)?;
    let res = hash.miller_rabin(cs.namespace(|| "primeck"), MILLER_RABIN_ROUNDS)?;
    Boolean::enforce_equal(cs.namespace(|| "result"), &Boolean::constant(true), &res)?;
    Ok(hash)
}

#[cfg(test)]
mod test {
    use num_bigint::BigUint;
    use sapling_crypto::bellman::pairing::ff::PrimeField;
    use sapling_crypto::bellman::{ConstraintSystem, SynthesisError};
    use sapling_crypto::circuit::num::AllocatedNum;
    use sapling_crypto::group_hash::Keccak256Hasher;
    use sapling_crypto::poseidon::bn256::Bn256PoseidonParams;
    use sapling_crypto::poseidon::{PoseidonEngine, QuinticSBox};

    use super::{hash_to_prime, helper};

    use bignat::BigNat;
    use hash::HashDomain;
    use OptionExt;

    use test_helpers::*;

    #[test]
    fn mr_11() {
        assert_eq!(helper::miller_rabin(&BigUint::from(11usize), 3), true);
    }

    #[test]
    fn mr_12() {
        assert_eq!(helper::miller_rabin(&BigUint::from(12usize), 3), false);
    }

    #[test]
    fn mr_251() {
        assert_eq!(helper::miller_rabin(&BigUint::from(251usize), 11), true);
    }

    #[test]
    fn mr_15() {
        assert_eq!(helper::miller_rabin(&BigUint::from(15usize), 3), false);
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
                helper::hash_to_prime::<E>(&input_values, &domain, &self.params.hash).unwrap();
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
            let hash = hash_to_prime(
                cs.namespace(|| "hash"),
                &allocated_inputs,
                32,
                &domain,
                &self.params.hash,
            )?;
            assert_eq!(
                hash.limbs.len() * hash.params.limb_width,
                self.params.desired_bits
            );
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
        prime_hash_one_32b: (PrimeHash {
            inputs: Some(
                        PrimeHashInputs {
                            inputs: &[
                                "1",
                            ],
                        }
                    ),
                    params: PrimeHashParams {
                        desired_bits: 32,
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
