use num_bigint::BigUint;
use sapling_crypto::bellman::pairing::ff::Field;
use sapling_crypto::bellman::{ConstraintSystem, LinearCombination, SynthesisError};
use sapling_crypto::circuit::boolean::Boolean;
use sapling_crypto::circuit::num::AllocatedNum;
use sapling_crypto::poseidon::{PoseidonEngine, PoseidonHashParams, QuinticSBox};

use bignat::BigNat;
use num::Num;
use OptionExt;

const MILLER_RABIN_ROUNDS: usize = 3;

pub const PRIMES_8_BIT: [u8; 23] = [
    0b10000011, 0b10001001, 0b10001011, 0b10010101, 0b10010111, 0b10011101, 0b10100011, 0b10100111,
    0b10101101, 0b10110011, 0b10110101, 0b10111111, 0b11000001, 0b11000101, 0b11000111, 0b11010011,
    0b11011111, 0b11100011, 0b11100101, 0b11101001, 0b11101111, 0b11110001, 0b11111011,
];

/// A representation of the hash of
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

fn miller_rabin_32b(n: &BigUint) -> bool {
    miller_rabin_round(n, &BigUint::from(2usize))
        || miller_rabin_round(n, &BigUint::from(7usize))
        || miller_rabin_round(n, &BigUint::from(61usize))
}

pub mod helper {

    use super::miller_rabin_32b;
    use super::HashDomain;
    use f_to_nat;
    use mimc::helper::mimc;
    use num_bigint::BigUint;
    use num_integer::Integer;
    use num_traits::{One, Zero};
    use sapling_crypto::bellman::pairing::ff::{Field, PrimeField};
    use sapling_crypto::poseidon::{
        poseidon_hash, PoseidonEngine, PoseidonHashParams, QuinticSBox,
    };

    /// Given an integer, returns the integer with its low `k` bits.
    fn low_k_bits(n: &BigUint, k: usize) -> BigUint {
        n & ((BigUint::one() << k) - 1usize)
    }

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

        // First we hash the inputs, using poseidon.
        let hash = poseidon_hash::<E>(params, inputs).pop().unwrap();

        // Then, to get more bits, we extend with MiMC
        let mut sum_of_hashes = low_k_bits(&f_to_nat(&hash), bits_per_hash);
        let mut perm = hash;
        for i in 1..n_hashes {
            perm.add_assign(&E::Fr::one());
            let low_bits = low_k_bits(&f_to_nat(&perm), bits_per_hash);
            sum_of_hashes += low_bits << (bits_per_hash * i);
        }

        // Now we assemble the 1024b number. Notice the ORs are all disjoint.
        let mut acc = (BigUint::one() << domain.n_trailing_ones) - 1usize;
        acc |= low_k_bits(&sum_of_hashes, bits_from_hash) << domain.n_trailing_ones;
        acc |= BigUint::one() << (domain.n_bits - 1);
        acc
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

    /// Given a target entropy, constructs a plan for how to make a prime number of that
    /// bitwidth that can be certified using a recursive Pocklington test.
    /// This is a list a_i such that is s_i is defined by s_0 = 8 + a_0 and s_i = s_{i-1} + a_i
    /// , then each a_i is less than its s_i, and s_n = 128
    pub fn pocklington_plan(entropy: usize) -> Vec<usize> {
        // (entropy, bits, extension)
        assert!(entropy >= 30);
        let mut table: Vec<(usize, usize, usize)> = vec![(30, 32, 0)];
        while table.last().unwrap().0 < entropy {
            let mut best_bits = std::usize::MAX;
            let mut extension_size_for_best = 0;
            let next_entropy = table.last().unwrap().0 + 1;
            for (prev_entropy, prev_bits, _) in table.as_slice().iter().rev() {
                let extension_bits = next_entropy - prev_entropy + 1;
                let total_bits = extension_bits + prev_bits;
                if extension_bits < *prev_bits {
                    if total_bits < best_bits {
                        best_bits = total_bits;
                        extension_size_for_best = extension_bits;
                    }
                } else {
                    break;
                }
            }
            table.push((next_entropy, best_bits, extension_size_for_best));
        }
        assert_eq!(table.last().unwrap().0, entropy);
        let mut i = table.len() - 1;
        let mut extensions = Vec::new();
        while i > 0 {
            extensions.push(table[i].2);
            i -= table[i].2 - 1;
        }
        extensions.reverse();
        extensions
    }

    #[derive(Debug, Clone, PartialEq, Eq)]
    pub enum PocklingtonCertificate {
        Base(BigUint),
        Recursive {
            rec: Box<PocklingtonCertificate>,
            extension: BigUint,
            base: BigUint,
            number: BigUint,
            nonce: usize,
        },
    }

    impl PocklingtonCertificate {
        pub fn number(&self) -> &BigUint {
            match &self {
                PocklingtonCertificate::Base(s) => s,
                PocklingtonCertificate::Recursive { number, .. } => number,
            }
        }
    }

    pub fn attempt_pocklington_extension<F: PrimeField>(
        p: PocklingtonCertificate,
        extension: BigUint,
    ) -> Result<PocklingtonCertificate, PocklingtonCertificate> {
        let nonce_bits = 10;
        for i in 0..(1 << nonce_bits) {
            let nonced_extension = &extension
                + 2usize
                    * low_k_bits(
                        &f_to_nat(&mimc(F::from_str(&format!("{}", i)).unwrap())),
                        nonce_bits,
                    );
            let number = p.number() * &nonced_extension + 1usize;
            let mut base = BigUint::from(2usize);
            while base < number {
                let part = base.modpow(&nonced_extension, &number);
                if part.modpow(p.number(), &number) != BigUint::from(1usize) {
                    break;
                }
                if (part - 1usize).gcd(&number).is_one() {
                    return Ok(PocklingtonCertificate::Recursive {
                        rec: Box::new(p),
                        extension: nonced_extension,
                        base,
                        number,
                        nonce: i,
                    });
                }
                base += 1usize;
            }
        }
        Err(p)
    }

    pub fn entropy_needed(plan: &[usize]) -> usize {
        plan.iter().map(|i| i - 1).sum::<usize>() + 4
    }

    pub struct EntropySource {
        bits: Vec<bool>,
    }

    impl EntropySource {
        pub fn new<F: PrimeField>(hash: F, bits_needed: usize) -> Self {
            let elems_needed = (bits_needed - 1) / F::CAPACITY as usize + 1;
            let mut elems = vec![hash];
            while elems.len() < elems_needed {
                elems.push(mimc(elems.last().unwrap().clone()));
            }
            let mut bits = Vec::new();
            for (i, hash) in elems.into_iter().enumerate() {
                let n = f_to_nat(&hash);
                bits.extend(
                    n.to_bytes_le()
                        .into_iter()
                        .flat_map(|byte| (0..8).map(move |i| (byte >> i) & 1 > 0)),
                );
                let ex_len = (i + 1) * (F::CAPACITY as usize);
                bits.truncate(ex_len);
                bits.extend(std::iter::repeat(false).take(ex_len - bits.len()));
            }
            Self { bits }
        }
        pub fn get_bit(&mut self) -> bool {
            self.bits.pop().unwrap()
        }
        pub fn get_bits_as_nat(&mut self, n_bits: usize) -> BigUint {
            let mut acc = BigUint::zero();
            for _ in 0..n_bits {
                acc = (acc << 1)
                    | if self.get_bit() {
                        BigUint::one()
                    } else {
                        BigUint::zero()
                    }
            }
            acc
        }
    }

    pub fn execute_pocklington_plan<F: PrimeField>(
        hash: F,
        plan: &[usize],
    ) -> Option<PocklingtonCertificate> {
        let mut bits = EntropySource::new(hash, entropy_needed(plan));
        let base_nat = (BigUint::one() << 31) | (bits.get_bits_as_nat(30) << 1) | BigUint::one();
        if !miller_rabin_32b(&base_nat) {
            return None;
        }
        let mut certificate = PocklingtonCertificate::Base(base_nat);
        for extension_bits in plan {
            let extension = bits.get_bits_as_nat(extension_bits - 1) << 1;
            certificate = attempt_pocklington_extension::<F>(certificate, extension).ok()?;
        }
        Some(certificate)
    }

    pub fn hash_to_pocklington_prime<E: PoseidonEngine<SBox = QuinticSBox<E>>>(
        inputs: &[E::Fr],
        entropy: usize,
        params: &E::Params,
    ) -> Option<(PocklingtonCertificate, E::Fr)> {
        let n_bits = 16;
        let plan = pocklington_plan(entropy);
        let mut inputs: Vec<E::Fr> = inputs.iter().copied().collect();
        inputs.push(E::Fr::zero());
        for _ in 0..(1 << n_bits) {
            let hash = poseidon_hash::<E>(params, &inputs).pop().unwrap();
            if let Some(cert) = execute_pocklington_plan(hash, &plan) {
                return Some((cert, inputs.last().unwrap().clone()));
            }
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

    // First we hash the inputs, with poseidon
    let hash = sapling_crypto::circuit::poseidon_hash::poseidon_hash(
        cs.namespace(|| "inputs"),
        &input,
        params,
    )?
    .pop()
    .unwrap();

    let mut hash_bits = hash.into_bits_le_strict(cs.namespace(|| "bitify"))?;
    hash_bits.truncate(bits_per_hash);

    // Then we extend with MiMC
    let mut perm = hash.clone();
    for i in 0..(n_hashes - 1) {
        let new = AllocatedNum::alloc(cs.namespace(|| format!("perm {}", i)), || {
            Ok({
                let mut t = perm.get_value().grab()?.clone();
                t.add_assign(&E::Fr::one());
                t
            })
        })?;
        cs.enforce(|| format!("correct perm {}", i),
            |lc| lc,
            |lc| lc,
            |lc| lc + new.get_variable() - perm.get_variable() - CS::one(),
        );
        perm = new;
        let low_bits: Vec<Boolean> = {
            let mut b = perm.into_bits_le_strict(cs.namespace(|| format!("bitify {}", i)))?;
            b.truncate(bits_per_hash);
            b
        };
        hash_bits.extend(low_bits);
    }

    let mut all_bits = Vec::new();
    all_bits.extend(std::iter::repeat(Boolean::Constant(true)).take(domain.n_trailing_ones));
    all_bits.extend(hash_bits.into_iter().take(bits_from_hash));
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
    .fits_in_bits(cs.namespace(|| "nonce bound"), domain.nonce_width())?;
    inputs.push(nonce);
    let hash = hash_to_rsa_element(cs.namespace(|| "hash"), &inputs, limb_width, domain, params)?;
    let res = hash.miller_rabin(cs.namespace(|| "primeck"), MILLER_RABIN_ROUNDS)?;
    Boolean::enforce_equal(cs.namespace(|| "result"), &Boolean::constant(true), &res)?;
    Ok(hash)
}

#[cfg(test)]
mod test {
    use super::*;

    use gadget::Gadget;
    use sapling_crypto::bellman::pairing::ff::ScalarEngine;
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
            assert_eq!(
                hash.limbs.len() * hash.params().limb_width,
                self.params.desired_bits
            );
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

    #[test]
    fn pocklington_plan_128() {
        assert_eq!(vec![31, 62, 8], helper::pocklington_plan(128));
    }

    use super::helper::PocklingtonCertificate::*;

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
                    let (cert, _nonce) = helper::hash_to_pocklington_prime::<Bn256>(&input_values, entropy, &params).expect("pocklington generation failed");
                    assert!(miller_rabin(cert.number(), 20));
                }
            )*
        }
    }

    pocklington_hash_tests! {
        pocklington_hash_128_1: (&["1"], 128),
        pocklington_hash_128_2: (&["2"], 128),
        pocklington_hash_128_3: (&["3"], 128),
        pocklington_hash_128_4: (&["4"], 128),
    }
}
