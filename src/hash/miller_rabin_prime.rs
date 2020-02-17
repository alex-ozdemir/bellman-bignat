use sapling_crypto::bellman::pairing::Engine;
use sapling_crypto::bellman::{ConstraintSystem, LinearCombination, SynthesisError};
use sapling_crypto::circuit::boolean::Boolean;
use sapling_crypto::circuit::num::AllocatedNum;

use super::circuit::CircuitHasher;
use super::integer::hash_to_integer;
use super::{HashDomain, Hasher};
use mp::bignat::BigNat;
use util::num::Num;
use OptionExt;

pub mod helper {
    use rug::Integer;
    use sapling_crypto::bellman::pairing::ff::Field;

    use super::super::integer::helper::hash_to_integer;
    use super::super::{HashDomain, Hasher};

    /// Returns whether `n` passes Miller-Rabin checks with the first `rounds` primes as bases
    pub fn miller_rabin(n: &Integer, rounds: usize) -> bool {
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
            .any(|p| !miller_rabin_round(n, &Integer::from(p)))
    }

    /// Returns whether `n` passes a Miller-Rabin check with base `b`.
    fn miller_rabin_round(n: &Integer, b: &Integer) -> bool {
        let n_less_one = Integer::from(n - 1);
        let mut d = Integer::from(n - 1);
        let d_bits = d.to_string_radix(2);
        let last_one = d_bits.as_str().rfind('1').expect("Input must be >1");
        if last_one == d_bits.len() - 1 {
            return false;
        }
        let s = d_bits.len() - last_one - 1;
        d >>= s as u32;
        let mut pow = Integer::from(b.pow_mod_ref(&d, &n).unwrap());
        if pow == Integer::from(1usize) || pow == n_less_one {
            return true;
        }
        for _ in 0..(s - 1) {
            pow.square_mut();
            pow %= n;
            if pow == n_less_one {
                return true;
            }
        }
        return false;
    }

    pub fn miller_rabin_32b(n: &Integer) -> bool {
        miller_rabin_round(n, &Integer::from(2usize))
            && miller_rabin_round(n, &Integer::from(7usize))
            && miller_rabin_round(n, &Integer::from(61usize))
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
    pub fn hash_to_prime<H: Hasher>(
        inputs: &[H::F],
        domain: &HashDomain,
        hasher: &H,
    ) -> Option<(Integer, H::F, usize)> {
        let n_bits = domain.nonce_width();
        let mut inputs: Vec<H::F> = inputs.iter().copied().collect();
        inputs.push(H::F::zero());
        for _ in 0..(1 << n_bits) {
            let hash = hash_to_integer::<H>(&inputs, domain, hasher);
            if miller_rabin(&hash, 30) {
                // unwrap is safe because of the push above
                return Some((hash, inputs.pop().unwrap(), n_bits));
            }
            // unwrap is safe because of the push above
            inputs.last_mut().unwrap().add_assign(&H::F::one());
        }
        None
    }
}

pub fn hash_to_prime<E, H, CS>(
    mut cs: CS,
    input: &[AllocatedNum<E>],
    limb_width: usize,
    domain: &HashDomain,
    hasher: &H,
    rounds: usize,
) -> Result<BigNat<E>, SynthesisError>
where
    E: Engine,
    H: CircuitHasher<E = E> + Hasher<F = E::Fr>,
    CS: ConstraintSystem<E>,
{
    if domain.n_trailing_ones < 2 {
        return Err(SynthesisError::Unsatisfiable);
    }
    let mut inputs: Vec<_> = input.iter().cloned().collect();
    let nonce = AllocatedNum::alloc(cs.namespace(|| "nonce"), || {
        let inputs = inputs
            .iter()
            .map(|i| i.get_value())
            .collect::<Option<Vec<E::Fr>>>();
        let (_, nonce, _) = helper::hash_to_prime::<H>(&inputs.grab()?, domain, hasher)
            .ok_or(SynthesisError::Unsatisfiable)?;
        Ok(nonce)
    })?;
    Num::new(
        nonce.get_value(),
        LinearCombination::zero() + nonce.get_variable(),
    )
    .fits_in_bits(cs.namespace(|| "nonce bound"), domain.nonce_width())?;
    inputs.push(nonce);
    let hash = hash_to_integer(cs.namespace(|| "hash"), &inputs, limb_width, domain, hasher)?;
    let res = hash.miller_rabin(cs.namespace(|| "primeck"), rounds)?;
    Boolean::enforce_equal(cs.namespace(|| "result"), &Boolean::constant(true), &res)?;
    Ok(hash)
}

#[cfg(test)]
mod test {
    use super::*;

    use rug::Integer;
    use sapling_crypto::bellman::pairing::ff::PrimeField;
    use sapling_crypto::bellman::{ConstraintSystem, SynthesisError};
    use sapling_crypto::circuit::num::AllocatedNum;

    use hash::hashes::Poseidon;
    use util::test_helpers::*;

    #[test]
    fn mr_11() {
        assert_eq!(helper::miller_rabin(&Integer::from(11usize), 3), true);
    }

    #[test]
    fn mr_12() {
        assert_eq!(helper::miller_rabin(&Integer::from(12usize), 3), false);
    }

    #[test]
    fn mr_251() {
        assert_eq!(helper::miller_rabin(&Integer::from(251usize), 11), true);
    }

    #[test]
    fn mr_15() {
        assert_eq!(helper::miller_rabin(&Integer::from(15usize), 3), false);
    }

    #[derive(Debug)]
    pub struct PrimeHashInputs<'a> {
        pub inputs: &'a [&'a str],
    }

    #[derive(Debug)]
    pub struct PrimeHashParams<H> {
        pub desired_bits: usize,
        pub hasher: H,
        pub n_rounds: usize,
    }

    pub struct PrimeHash<'a, H> {
        inputs: Option<PrimeHashInputs<'a>>,
        params: PrimeHashParams<H>,
    }

    impl<'a, E: Engine, H: Hasher<F = E::Fr> + CircuitHasher<E = E>> Circuit<E> for PrimeHash<'a, H> {
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
                helper::hash_to_prime(&input_values, &domain, &self.params.hasher).unwrap();
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
                &self.params.hasher,
                self.params.n_rounds,
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
                        hasher: Poseidon::default(),
                        n_rounds: 3,
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
                        hasher: Poseidon::default(),
                        n_rounds: 3,
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
                        hasher: Poseidon::default(),
                        n_rounds: 3,
                    }
        }, true),
    }
}
