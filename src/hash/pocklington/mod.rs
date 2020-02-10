mod entropy;

pub mod helper {

    use num_bigint::BigUint;
    use num_integer::Integer;
    use num_iter::range_step;
    use num_traits::One;
    use sapling_crypto::bellman::pairing::ff::PrimeField;

    use super::entropy::helper::EntropySource;
    use super::entropy::NatTemplate;
    use hash::miller_rabin_prime::helper::miller_rabin_32b;
    use hash::Hasher;

    use std::cmp::min;

    #[derive(Debug, Clone, PartialEq, Eq)]
    pub struct PocklingtonPlan {
        /// Number of nonce bits in the base prime
        pub base_nonce_bits: usize,
        /// Number of random bits in the base prime
        pub base_random_bits: usize,
        pub extensions: Vec<PlannedExtension>,
    }

    /// A pocklington extension multiplies a base prime by a term
    ///
    ///( 1 || r || n )
    ///
    /// , producing
    ///
    /// p' = p * (1 || r || n) + 1
    ///
    /// such that `p'` is prime.
    ///
    /// This structure stores the plan: the size of `r` and `n`.
    #[derive(Debug, Clone, PartialEq, Eq)]
    pub struct PlannedExtension {
        pub nonce_bits: usize,
        pub random_bits: usize,
    }

    impl PlannedExtension {
        pub fn max_value(&self) -> BigUint {
            (BigUint::one() << (self.nonce_bits + self.random_bits + 1)) - 1usize
        }
        pub fn min_value(&self) -> BigUint {
            BigUint::one() << (self.nonce_bits + self.random_bits)
        }
        pub fn evaluate(&self, random_value: &BigUint, nonce_value: u64) -> BigUint {
            assert!(self.nonce_bits <= 64);
            self.min_value() + (random_value << self.nonce_bits) + nonce_value
        }
    }

    /// Returns the probability that a number with `bits` bits is prime
    fn prime_density(bits: usize) -> f64 {
        let log2e = std::f64::consts::E.log2();
        let b = bits as f64;
        log2e / b - log2e * log2e / b / b
    }

    /// Returns the number of random `bits`-bit numbers that must be checked to find a prime with
    /// all but `p_fail` probability
    pub fn prime_trials(bits: usize, p_fail: f64) -> usize {
        let p = prime_density(bits);
        (p_fail.log(1.0 - p).ceil() + 0.1) as usize
    }

    /// The number of nonce bits needed to generate a `bits`-bit prime with all but 2**-64
    /// probability.
    pub fn nonce_bits_needed(bits: usize) -> usize {
        let trials = prime_trials(bits, 2.0f64.powi(-64));
        ((trials as f64).log2().ceil() + 0.1) as usize
    }

    impl PocklingtonPlan {
        /// Given a target entropy, constructs a plan for how to make a prime number of that
        /// bitwidth that can be certified using a recursive Pocklington test.
        pub fn new(entropy: usize) -> Self {
            // Less than 31
            // Since we fix both low bits of the base prime to 1, we need an extra nonce bit, since
            // the 2's place bit is artificially fixed.
            let nonce_bits_needed_in_base = nonce_bits_needed(32) + 1;
            let mut plan = Self {
                base_nonce_bits: nonce_bits_needed_in_base,
                // High bit is fixed to 1, so 31 bits for the nonce/random bits.
                base_random_bits: min(entropy, 31 - nonce_bits_needed_in_base),
                extensions: Vec::new(),
            };

            while plan.entropy() < entropy {
                // If the extension has this many bits it is guaranteed to be less than the current
                // base.
                let max_extension_bits = plan.min_value().bits() - 1;
                // Now, how many of those need to be nonce.
                // TODO We could get a tighter bound by using max values, and not bits.
                let max_nonce_bits_needed = nonce_bits_needed(max_extension_bits + plan.max_bits());
                assert!(max_nonce_bits_needed < max_extension_bits);
                let max_random_bits = max_extension_bits - max_nonce_bits_needed - 1;
                let random_bits = min(entropy - plan.entropy(), max_random_bits);
                // TODO we might be able to omit a nonce bit if we were to re-compute the nonce
                // width using `random_bits`.
                plan.extensions.push(PlannedExtension {
                    nonce_bits: max_nonce_bits_needed,
                    random_bits: random_bits,
                })
                // TODO these TODOs are worth looking at because we currently require 321 bits for
                // a 256b nonce, which is just bigger than a multiple of 32.
            }

            plan
        }

        pub fn entropy(&self) -> usize {
            self.extensions.iter().map(|i| i.random_bits).sum::<usize>() + self.base_random_bits
        }

        pub fn max_value(&self) -> BigUint {
            self.extensions.iter().fold(
                (BigUint::one() << (self.base_random_bits + self.base_nonce_bits + 1)) - 1usize,
                |acc, ext| acc * ext.max_value() + 1usize,
            )
        }

        pub fn min_value(&self) -> BigUint {
            self.extensions.iter().fold(
                BigUint::one() << (self.base_random_bits + self.base_nonce_bits),
                |acc, ext| acc * ext.min_value() + 1usize,
            )
        }

        pub fn max_bits(&self) -> usize {
            self.max_value().bits()
        }
    }

    #[derive(Debug, Clone, PartialEq, Eq)]
    pub struct PocklingtonExtension {
        pub plan: PlannedExtension,
        pub random: BigUint,
        pub nonce: u64,
        pub checking_base: BigUint,
        pub result: BigUint,
    }

    #[derive(Debug, Clone, PartialEq, Eq)]
    pub struct PocklingtonCertificate {
        pub base_prime: BigUint,
        pub base_nonce: usize,
        pub extensions: Vec<PocklingtonExtension>,
    }

    impl PocklingtonCertificate {
        pub fn number(&self) -> &BigUint {
            if let Some(l) = self.extensions.last() {
                &l.result
            } else {
                &self.base_prime
            }
        }
    }

    pub fn attempt_pocklington_base(
        plan: &PocklingtonPlan,
        entropy_source: &mut EntropySource,
    ) -> Option<PocklingtonCertificate> {
        let random = entropy_source.get_bits_as_nat(
            NatTemplate::with_random_bits(plan.base_random_bits).with_leading_ones(1),
        );
        for nonce in 0..(1u64 << plan.base_nonce_bits) {
            if (nonce & 0b11) == 0b11 {
                let base = (&random << plan.base_nonce_bits) + nonce;
                if miller_rabin_32b(&base) {
                    return Some(PocklingtonCertificate {
                        base_prime: base,
                        base_nonce: nonce as usize,
                        extensions: Vec::new(),
                    });
                }
            }
        }
        None
    }

    pub fn attempt_pocklington_extension<F: PrimeField>(
        mut p: PocklingtonCertificate,
        plan: &PlannedExtension,
        entropy_source: &mut EntropySource,
    ) -> Option<PocklingtonCertificate> {
        let random =
            entropy_source.get_bits_as_nat(NatTemplate::with_random_bits(plan.random_bits));
        for nonce in 0..(1u64 << plan.nonce_bits) {
            let extension = plan.evaluate(&random, nonce);
            let number = p.number() * &extension + 1usize;
            for base in range_step(BigUint::from(2usize), number.clone(), BigUint::one()) {
                let part = base.modpow(&extension, &number);
                if part.modpow(p.number(), &number) != BigUint::from(1usize) {
                    break;
                }
                if (&part - 1usize).gcd(&number).is_one() {
                    p.extensions.push(PocklingtonExtension {
                        plan: plan.clone(),
                        random,
                        checking_base: base,
                        result: number,
                        nonce,
                    });
                    return Some(p);
                }
            }
        }
        None
    }

    pub fn hash_to_pocklington_prime<H: Hasher>(
        inputs: &[H::F],
        entropy: usize,
        base_hash: &H,
    ) -> Option<PocklingtonCertificate> {
        let plan = PocklingtonPlan::new(entropy);
        let inputs: Vec<H::F> = inputs.iter().copied().collect();
        let hash = base_hash.hash(&inputs);
        let mut entropy_source = EntropySource::new(hash, plan.entropy());
        let mut cert = attempt_pocklington_base(&plan, &mut entropy_source)?;
        for extension in &plan.extensions {
            cert = attempt_pocklington_extension::<H::F>(cert, extension, &mut entropy_source)?;
        }
        Some(cert)
    }

    #[cfg(test)]
    mod test {
        use super::*;

        #[test]
        fn prime_prob_64b() {
            let p = prime_density(64);
            assert!(p >= 0.02);
            assert!(p <= 0.03);
        }

        #[test]
        fn prime_trials_64b() {
            let t = prime_trials(64, (2.0f64).powi(64));
            assert!(t >= 1000);
            assert!(t <= 1100);
        }
    }
}

use num_bigint::BigUint;
use num_traits::One;
use sapling_crypto::bellman::pairing::ff::Field;
use sapling_crypto::bellman::pairing::Engine;
use sapling_crypto::bellman::{ConstraintSystem, SynthesisError};
use sapling_crypto::circuit::boolean::Boolean;
use sapling_crypto::circuit::num::AllocatedNum;

use self::entropy::{EntropySource, NatTemplate};
use hash::circuit::CircuitHasher;
use hash::Hasher;
use mp::bignat::{BigNat, BigNatParams};
use util::convert::usize_to_f;
use util::gadget::Gadget;
use util::num::Num;
use OptionExt;

pub fn hash_to_pocklington_prime<
    E: Engine,
    H: Hasher<F = E::Fr> + CircuitHasher<E = E>,
    CS: ConstraintSystem<E>,
>(
    mut cs: CS,
    input: &[AllocatedNum<E>],
    limb_width: usize,
    entropy: usize,
    base_hash: &H,
) -> Result<BigNat<E>, SynthesisError> {
    use self::helper::{PocklingtonCertificate, PocklingtonPlan};

    // Hash the inputs into an entropy pool.
    let hash = base_hash.allocate_hash(cs.namespace(|| "base hash"), &input)?;
    let mut entropy_source =
        EntropySource::alloc(cs.namespace(|| "entropy source"), Some(&()), hash, &entropy)?;

    // Construct a pocklington plan, and a certificate if we actually have values.
    let plan = PocklingtonPlan::new(entropy);
    let cert: Option<PocklingtonCertificate> = input
        .iter()
        .map(|n| n.get_value().clone())
        .collect::<Option<Vec<E::Fr>>>()
        .and_then(|is| helper::hash_to_pocklington_prime(&is, entropy, base_hash));

    // Allocate the base nonce.
    let base_nonce = BigNat::from_num(
        Num::from(AllocatedNum::alloc(cs.namespace(|| "base nonce"), || {
            Ok(usize_to_f(cert.as_ref().grab()?.base_nonce as usize))
        })?),
        BigNatParams {
            n_limbs: 1, // TODO consider allowing larger nonces
            limb_width: limb_width,
            max_word: BigUint::one() << plan.base_nonce_bits,
            min_bits: 0,
        },
    );

    // Construct the base prime.
    let mut prime = entropy_source
        .get_bits_as_nat::<CS>(
            NatTemplate::with_random_bits(plan.base_random_bits)
                .with_leading_ones(1)
                .with_trailing(false, plan.base_nonce_bits),
            limb_width,
        )
        .add::<CS>(&base_nonce)?;

    // Check it
    let mr_res = &prime.miller_rabin_32b(cs.namespace(|| "base check"))?;
    Boolean::enforce_equal(
        cs.namespace(|| "MR passes"),
        &mr_res,
        &Boolean::constant(true),
    )?;

    // For each extension...
    for (i, extension) in plan.extensions.into_iter().enumerate() {
        let mut cs = cs.namespace(|| format!("extension {}", i));

        // Allocate the nonce
        let nonce = BigNat::from_num(
            Num::from(AllocatedNum::alloc(cs.namespace(|| "nonce"), || {
                Ok(usize_to_f(
                    cert.as_ref().grab()?.extensions[i].nonce as usize,
                ))
            })?),
            BigNatParams {
                n_limbs: 1, // TODO consider allowing larger nonces
                limb_width: prime.params.limb_width,
                max_word: BigUint::one() << extension.nonce_bits,
                min_bits: 0,
            },
        );

        // Allocate the nonce
        let extension = entropy_source
            .get_bits_as_nat::<CS>(
                NatTemplate::with_random_bits(extension.random_bits)
                    .with_leading_ones(1)
                    .with_trailing(false, extension.nonce_bits),
                limb_width,
            )
            .add::<CS>(&nonce)?;
        let base = BigNat::alloc_from_nat(
            cs.namespace(|| "base"),
            || {
                Ok(BigUint::from(
                    cert.as_ref().grab()?.extensions[i].checking_base.clone(),
                ))
            },
            limb_width,
            1, // TODO consider allow larger bases
        )?;

        // Compute helper values for pocklington's criterion
        let n_less_one = extension.mult(cs.namespace(|| "n - 1"), &prime)?;
        let n = n_less_one.shift::<CS>(E::Fr::one());
        let part = base.pow_mod(cs.namespace(|| "a^r"), &extension, &n)?;
        let one = BigNat::one(cs.namespace(|| "one"), prime.params().limb_width)?;
        let part_less_one = part.sub(cs.namespace(|| "a^r - 1"), &one)?;

        // Check coprimality
        part_less_one.enforce_coprime(cs.namespace(|| "coprime"), &n)?;
        let power = part.pow_mod(cs.namespace(|| "a^r^p"), &prime, &n)?;

        // Check fermat's little theorem
        power.equal_when_carried(cs.namespace(|| "a^r^p == 1"), &one)?;

        // NB: The "less than" condition is enforced by the bitwidths and the min-value analysis.

        prime = n;
    }
    Ok(prime)
}

#[cfg(test)]
mod test {
    use super::{hash_to_pocklington_prime, helper};
    use sapling_crypto::bellman::pairing::ff::{PrimeField, ScalarEngine};
    use sapling_crypto::bellman::pairing::Engine;
    use sapling_crypto::bellman::{ConstraintSystem, SynthesisError};
    use sapling_crypto::circuit::num::AllocatedNum;

    use hash::circuit::CircuitHasher;
    use hash::hashes::Poseidon;
    use hash::{miller_rabin_prime, Hasher};
    use mp::bignat::BigNat;
    use OptionExt;

    use util::test_helpers::*;

    #[test]
    fn pocklington_plan_128() {
        let p = helper::PocklingtonPlan::new(128);
        println!("{:#?}", p);
        println!("{:#?}", p.max_bits());
        assert_eq!(p.entropy(), 128);
    }

    #[test]
    fn pocklington_plan_256() {
        let p = helper::PocklingtonPlan::new(256);
        println!("{:#?}", p);
        println!("{:#?}", p.max_bits());
        assert_eq!(p.entropy(), 256);
    }

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
                    let hash = Poseidon::<Bn256>::default();
                    let cert = helper::hash_to_pocklington_prime(&input_values, entropy, &hash).expect("pocklington generation failed");
                    assert!(miller_rabin_prime::helper::miller_rabin(cert.number(), 20));
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
    pub struct PockHashParams<H> {
        pub entropy: usize,
        pub hash: H,
    }

    pub struct PockHash<'a, H> {
        inputs: Option<PockHashInputs<'a>>,
        params: PockHashParams<H>,
    }

    impl<'a, E: Engine, H: Hasher<F = E::Fr> + CircuitHasher<E = E>> Circuit<E> for PockHash<'a, H> {
        fn synthesize<CS: ConstraintSystem<E>>(self, cs: &mut CS) -> Result<(), SynthesisError> {
            let input_values: Vec<E::Fr> = self
                .inputs
                .grab()?
                .inputs
                .iter()
                .map(|s| E::Fr::from_str(s).unwrap())
                .collect();
            let cert = helper::hash_to_pocklington_prime(
                &input_values,
                self.params.entropy,
                &self.params.hash,
            )
            .expect("pocklington hash failed");
            let plan = helper::PocklingtonPlan::new(self.params.entropy);
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
            let hash = hash_to_pocklington_prime(
                cs.namespace(|| "hash"),
                &allocated_inputs,
                32,
                self.params.entropy,
                &self.params.hash,
            )?;
            println!(
                "Pocklington bits in: [{}, {}]",
                hash.params.min_bits,
                hash.params.limb_width * hash.params.n_limbs
            );
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
                    hash: Poseidon::default(),
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
                    hash: Poseidon::default(),
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
                    hash: Poseidon::default(),
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
                    hash: Poseidon::default(),
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
                    hash: Poseidon::default(),
                },
            },
            true,
        ),
        pocklington_hash_256_1: (
            PockHash {
                inputs: Some(PockHashInputs {
                    inputs: &["1","2","3","4","5","6","7","8","9","10"],
                }),
                params: PockHashParams {
                    entropy: 256,
                    hash: Poseidon::default(),
                },
            },
            true,
        ),
    }
}
