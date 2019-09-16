const NONCE_BITS: usize = 10;

pub mod helper {

    use super::NONCE_BITS;
    use hash::helper::low_k_bits;
    use hash::miller_rabin_prime::helper::miller_rabin_32b;
    use entropy::helper::EntropySource;
    use entropy::NatTemplate;
    use f_to_nat;
    use mimc::helper::mimc;
    use num_bigint::BigUint;
    use num_integer::Integer;
    use num_traits::One;
    use sapling_crypto::bellman::pairing::ff::{Field, PrimeField};
    use sapling_crypto::poseidon::{
        poseidon_hash, PoseidonEngine, QuinticSBox,
    };

    #[derive(Debug, Clone, PartialEq, Eq)]
    pub struct PocklingtonPlan {
        pub extensions: Vec<usize>,
    }

    impl PocklingtonPlan {
        /// Given a target entropy, constructs a plan for how to make a prime number of that
        /// bitwidth that can be certified using a recursive Pocklington test.
        pub fn new(entropy: usize) -> Self {
            // (entropy, bits, extension)
            assert!(entropy >= 29);
            let mut table: Vec<(usize, usize, usize)> = vec![(29, 32, 0)];
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
            Self { extensions }
        }

        pub fn entropy(&self) -> usize {
            self.extensions.iter().map(|i| i - 1).sum::<usize>() + 29
        }

        pub fn max_bits(&self) -> usize {
            self.extensions.iter().sum::<usize>() + 32
        }
    }

    #[derive(Debug, Clone, PartialEq, Eq)]
    pub struct PocklingtonExtension {
        pub extension: BigUint,
        pub base: BigUint,
        pub number: BigUint,
        pub nonce: usize,
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
                &l.number
            } else {
                &self.base_prime
            }
        }
    }

    pub fn attempt_pocklington_extension<F: PrimeField>(
        mut p: PocklingtonCertificate,
        extension: BigUint,
    ) -> Result<PocklingtonCertificate, PocklingtonCertificate> {
        for i in 0..(1 << NONCE_BITS) {
            let nonce = i;
            let mimcd_nonce = low_k_bits(&f_to_nat(&mimc(F::from_str(&format!("{}", i)).unwrap())), NONCE_BITS);
            let nonced_extension = (&extension + &mimcd_nonce) * 2usize;
            let number = p.number() * &nonced_extension + 1usize;
            let mut base = BigUint::from(2usize);
            while base < number {
                let part = base.modpow(&nonced_extension, &number);
                if part.modpow(p.number(), &number) != BigUint::from(1usize) {
                    break;
                }
                if (&part - 1usize).gcd(&number).is_one() {
                    p.extensions.push(PocklingtonExtension {
                        extension,
                        base,
                        number,
                        nonce,
                    });
                    return Ok(p);
                }
                base += 1usize;
            }
        }
        Err(p)
    }

    pub fn execute_pocklington_plan<F: PrimeField>(
        hash: F,
        plan: &PocklingtonPlan,
        nonce: usize,
    ) -> Option<PocklingtonCertificate> {
        let mut bits = EntropySource::new(hash, plan.entropy());
        let base_nat = bits.get_bits_as_nat(NatTemplate {
            trailing_ones: 2,
            leading_ones: 1,
            random_bits: 29,
        });
        if !miller_rabin_32b(&base_nat) {
            return None;
        }
        let mut certificate = PocklingtonCertificate {
            base_prime: base_nat,
            base_nonce: nonce,
            extensions: Vec::new(),
        };
        for extension_bits in &plan.extensions {
            let extension = bits.get_bits_as_nat(NatTemplate {
                random_bits: extension_bits - 1,
                trailing_ones: 0,
                leading_ones: 0,
            });
            certificate = attempt_pocklington_extension::<F>(certificate, extension).ok()?;
        }
        Some(certificate)
    }

    pub fn hash_to_pocklington_prime<E: PoseidonEngine<SBox = QuinticSBox<E>>>(
        inputs: &[E::Fr],
        entropy: usize,
        params: &E::Params,
    ) -> Option<PocklingtonCertificate> {
        let plan = PocklingtonPlan::new(entropy);
        let mut inputs: Vec<E::Fr> = inputs.iter().copied().collect();
        inputs.push(E::Fr::zero());
        for nonce in 0..(1 << NONCE_BITS) {
            let hash = poseidon_hash::<E>(params, &inputs).pop().unwrap();
            if let Some(cert) = execute_pocklington_plan(hash, &plan, nonce) {
                return Some(cert);
            }
            inputs.last_mut().unwrap().add_assign(&E::Fr::one());
        }
        None
    }
}

use num_bigint::BigUint;
use num_traits::One;
use sapling_crypto::bellman::pairing::ff::Field;
use sapling_crypto::bellman::{ConstraintSystem, SynthesisError};
use sapling_crypto::circuit::boolean::Boolean;
use sapling_crypto::circuit::num::AllocatedNum;
use sapling_crypto::circuit::poseidon_hash::poseidon_hash;
use sapling_crypto::poseidon::{PoseidonEngine, QuinticSBox};

use OptionExt;
use bignat::BigNat;
use entropy::{EntropySource, NatTemplate};
use gadget::Gadget;
use mimc::mimc;
use num::Num;
use usize_to_f;

pub fn hash_to_pocklington_prime<
    E: PoseidonEngine<SBox = QuinticSBox<E>>,
    CS: ConstraintSystem<E>,
>(
    mut cs: CS,
    input: &[AllocatedNum<E>],
    limb_width: usize,
    entropy: usize,
    params: &E::Params,
) -> Result<BigNat<E>, SynthesisError> {
    use self::helper::{PocklingtonCertificate, PocklingtonPlan};
    let plan = PocklingtonPlan::new(entropy);
    let cert: Option<PocklingtonCertificate> = input
        .iter()
        .map(|n| n.get_value().clone())
        .collect::<Option<Vec<E::Fr>>>()
        .and_then(|is| helper::hash_to_pocklington_prime::<E>(&is, entropy, params));
    let base_nonce = AllocatedNum::alloc(cs.namespace(|| "nonce"), || {
        Ok(usize_to_f::<E::Fr>(cert.as_ref().grab()?.base_nonce))
    })?;
    let mut inputs = input.to_vec();
    inputs.push(base_nonce);
    let hash = poseidon_hash::<E, _>(cs.namespace(|| "base hash"), &inputs, params)?
        .pop()
        .unwrap();
    let mut entropy_source =
        EntropySource::alloc(cs.namespace(|| "entropy source"), Some(&()), hash, &entropy)?;

    let mut prime = entropy_source.get_bits_as_nat::<CS>(
        NatTemplate {
            trailing_ones: 2,
            leading_ones: 1,
            random_bits: 29,
        },
        limb_width,
    );
    let mr_res = &prime.miller_rabin_32b(cs.namespace(|| "base check"))?;
    Boolean::enforce_equal(
        cs.namespace(|| "MR passes"),
        &mr_res,
        &Boolean::constant(true),
    )?;
    for (i, extension_bits) in plan.extensions.into_iter().enumerate() {
        let mut cs = cs.namespace(|| format!("extension {}", i));
        let nonce = AllocatedNum::alloc(cs.namespace(|| "nonce"), || {
            Ok(usize_to_f(cert.as_ref().grab()?.extensions[i].nonce))
        })?;
        let mimcd_nonce_all_bits = Num::from(mimc(cs.namespace(|| "mimc"), nonce)?);
        let mimcd_nonce = BigNat::from_num(
            mimcd_nonce_all_bits.low_k_bits(cs.namespace(|| "mimc low bits"), NONCE_BITS)?,
            crate::bignat::BigNatParams {
                n_limbs: 1,
                limb_width: prime.params.limb_width,
                max_word: BigUint::one() << NONCE_BITS,
                min_bits: 0,
            },
        );
        let extension = entropy_source.get_bits_as_nat::<CS>(
            NatTemplate {
                random_bits: extension_bits - 1,
                trailing_ones: 0,
                leading_ones: 0,
            },
            limb_width,
        );
        let nonced_extension = extension.add::<CS>(&mimcd_nonce)?.scale::<CS>(usize_to_f(2usize));
        let base = BigNat::alloc_from_nat(
            cs.namespace(|| "base"),
            || {
                Ok(BigUint::from(
                    cert.as_ref().grab()?.extensions[i].base.clone(),
                ))
            },
            limb_width,
            1, // TODO allow larger bases
        )?;
        let n_less_one = nonced_extension.mult(cs.namespace(|| "n - 1"), &prime)?;
        let n = n_less_one.shift::<CS>(E::Fr::one());
        let part = base.pow_mod(cs.namespace(|| "a^r"), &nonced_extension, &n)?;
        let one = BigNat::one(cs.namespace(|| "one"), prime.params().limb_width)?;
        let part_less_one = part.sub(cs.namespace(|| "a^r - 1"), &one)?;
        part_less_one.enforce_coprime(cs.namespace(|| "coprime"), &n)?;
        let power = part.pow_mod(cs.namespace(|| "a^r^p"), &prime, &n)?;
        power.equal_when_carried(cs.namespace(|| "a^r^p == 1"), &one)?;
        prime = n;
    }
    Ok(prime)
}

#[cfg(test)]
mod test {
    use super::{helper, hash_to_pocklington_prime};
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
            helper::PocklingtonPlan::new(128).extensions
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
                    let cert = helper::hash_to_pocklington_prime::<Bn256>(&input_values, entropy, &params).expect("pocklington generation failed");
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
            let cert = helper::hash_to_pocklington_prime::<E>(
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