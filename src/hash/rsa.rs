use num_bigint::BigUint;
use sapling_crypto::bellman::pairing::ff::Field;
use sapling_crypto::bellman::pairing::Engine;
use sapling_crypto::bellman::{ConstraintSystem, SynthesisError};
use sapling_crypto::circuit::boolean::Boolean;
use sapling_crypto::circuit::num::AllocatedNum;
use sapling_crypto::poseidon::{PoseidonEngine, PoseidonHashParams, QuinticSBox};

    use std::str::FromStr;

use OptionExt;
use bignat::BigNat;
use num::Num;
use super::HashDomain;
use bit::{Bit, Bitvector};
use wesolowski::Reduced;

const OFFSET_2048: &str = "30731438344250145947882657666206403727243332864808664054575262055190442942812700108124167942976653745028212341196692947492080562974589240558404052155436479139607283861572110186639866316589725954212169900473106847592072353357762907262662369230376196184226071545259316873351199416881666739376881925207433619609913435128355340248285568061176332195286623104126482371089555666194830543043595601648501184952472930075767818065617175977748228906417030406830990961578747315754348300610520710090878042950122953510395835606916522592211024941845938097013497415239566963754154588561352876059012472806373183052035005766579987123343";
const OFFSET_512: &str = "12260090376946711734120031891656796026361161089996129826004640183990021905572572824302484514470302046195674460977677239638547760386187660404531883140339307";
const OFFSET_128: &str = "320302797835264872593630364493262722277";

pub mod helper {
    use f_to_nat;
    use hash::helper::low_k_bits;
    use hash::HashDomain;
    use num_bigint::BigUint;
    use num_traits::{One};
    use sapling_crypto::bellman::pairing::ff::Field;
    use sapling_crypto::poseidon::{
        poseidon_hash, PoseidonEngine, PoseidonHashParams, QuinticSBox,
    };

    pub fn hash_to_integer<E: PoseidonEngine<SBox = QuinticSBox<E>>>(
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

    pub fn hash_to_rsa_element<E: PoseidonEngine<SBox = QuinticSBox<E>>>(
        inputs: &[E::Fr],
        offset: &BigUint,
        domain: &HashDomain,
        limb_width: usize,
        params: &E::Params,
    ) -> BigUint {
        assert_eq!(params.output_len(), 1);
        assert_eq!(params.security_level(), 126);
        let bits_per_hash = params.security_level() as usize * 2;
        assert!(domain.n_bits % limb_width == 0);
        let hash: E::Fr = sapling_crypto::poseidon::poseidon_hash::<E>(params, &inputs)
            .pop()
            .unwrap();
        let x = low_k_bits(&f_to_nat(&hash), bits_per_hash);
        offset + x
    }
}

pub fn offset(bit_width: usize) -> BigUint {
    BigUint::from_str(match bit_width {
        128 => OFFSET_128,
        512 => OFFSET_512,
        2048 => OFFSET_2048,
        n => panic!("Unsupported RSA bit_width: {}", n)
    }).unwrap()
}

pub fn allocate_offset<E: Engine, CS: ConstraintSystem<E>>(
    mut cs: CS,
    challenge: &BigNat<E>,
    bit_width: usize,
) -> Result<Reduced<E>, SynthesisError> {
    let n = offset(bit_width);
    let offset = BigNat::alloc_from_nat(
        cs.namespace(|| "OFFSET"),
        || Ok(n),
        challenge.params.limb_width,
        2047 / challenge.params.limb_width + 1,
    )?;
    let reduced = offset.red_mod(cs.namespace(|| "% l"), &challenge)?;
    Ok(Reduced {
        raw: offset,
        reduced,
    })
}

pub fn hash_to_integer<E: PoseidonEngine<SBox = QuinticSBox<E>>, CS: ConstraintSystem<E>>(
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
        cs.enforce(
            || format!("correct perm {}", i),
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

pub fn hash_to_rsa_element<E: PoseidonEngine<SBox = QuinticSBox<E>>, CS: ConstraintSystem<E>>(
    mut cs: CS,
    input: &[AllocatedNum<E>],
    limb_width: usize,
    domain: &HashDomain,
    offset: Reduced<E>,
    params: &E::Params,
) -> Result<BigNat<E>, SynthesisError> {
    if params.output_len() != 1 && params.security_level() != 126 {
        return Err(SynthesisError::Unsatisfiable);
    }
    let bits_per_hash = params.security_level() as usize * 2;
    assert!(domain.n_bits % limb_width == 0);
        let hash = sapling_crypto::circuit::poseidon_hash::poseidon_hash(
            cs.namespace(|| "inputs"),
            &input,
            params,
        )?
        .pop()
        .unwrap();
        let hash_bits = hash.into_bits_le_strict(cs.namespace(|| "bitify"))?;
    let bits: Vec<Boolean> = hash_bits.into_iter().take(bits_per_hash).collect();
    let x = BigNat::<E>::recompose(&Bitvector::from_bits(bits.into_iter().map(|b| Bit::from_sapling::<CS>(b)).collect()), limb_width);
    x.add::<CS>(&offset.raw)
}

pub fn hash_to_modded_rsa_element<E: PoseidonEngine<SBox = QuinticSBox<E>>, CS: ConstraintSystem<E>>(
    mut cs: CS,
    input: &[AllocatedNum<E>],
    limb_width: usize,
    domain: &HashDomain,
    offset: &Reduced<E>,
    challenge: &BigNat<E>,
    params: &E::Params,
) -> Result<Reduced<E>, SynthesisError> {
    if params.output_len() != 1 && params.security_level() != 126 {
        return Err(SynthesisError::Unsatisfiable);
    }
    let bits_per_hash = params.security_level() as usize * 2;
    assert!(domain.n_bits % limb_width == 0);
        let hash = sapling_crypto::circuit::poseidon_hash::poseidon_hash(
            cs.namespace(|| "inputs"),
            &input,
            params,
        )?
        .pop()
        .unwrap();
        let hash_bits = hash.into_bits_le_strict(cs.namespace(|| "bitify"))?;
    let bits: Vec<Boolean> = hash_bits.into_iter().take(bits_per_hash).collect();
    let x = BigNat::<E>::recompose(&Bitvector::from_bits(bits.into_iter().map(|b| Bit::from_sapling::<CS>(b)).collect()), limb_width);
    let r = x.red_mod(cs.namespace(|| "x % l"), challenge)?.add::<CS>(&offset.reduced)?;
    Ok(Reduced {
        raw: offset.raw.add::<CS>(&x)?,
        reduced: r,
    })
}

#[cfg(test)]
mod test {
    use hash::HashDomain;
    use num_bigint::BigUint;
    use sapling_crypto::bellman::pairing::ff::{PrimeField};
    use sapling_crypto::bellman::{ConstraintSystem, SynthesisError};
    use sapling_crypto::circuit::num::AllocatedNum;
    use sapling_crypto::group_hash::Keccak256Hasher;
    use sapling_crypto::poseidon::bn256::Bn256PoseidonParams;
    use sapling_crypto::poseidon::{PoseidonEngine, QuinticSBox};

    use std::str::FromStr;


    use bignat::BigNat;
    use OptionExt;

    use test_helpers::*;

    #[derive(Debug)]
    pub struct RsaHashInputs<'a> {
        pub inputs: &'a [&'a str],
    }

    #[derive(Debug)]
    pub struct RsaHashParams<E: PoseidonEngine<SBox = QuinticSBox<E>>> {
        pub desired_bits: usize,
        pub limb_width: usize,
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
            let cv = BigUint::from_str("5104102027859293093184735748236254201176269103281996090807").unwrap();
            let challenge = BigNat::alloc_from_nat(
                cs.namespace(|| "challenge"),
                || Ok(cv.clone()),
                32,
                6,
            )?;
            let offset = super::allocate_offset(cs.namespace(|| "offset"), &challenge, 2048)?;
            let expected_ouput = super::helper::hash_to_rsa_element::<E>(
                &input_values,
                offset.raw.value.as_ref().unwrap(),
                &HashDomain {
                    n_bits: self.params.desired_bits,
                    n_trailing_ones: 1,
                },
                self.params.limb_width,
                &self.params.hash,
            ) % &cv;


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
            let hash = super::hash_to_modded_rsa_element(
                cs.namespace(|| "hash"),
                &allocated_inputs,
                32,
                &HashDomain {
                    n_bits: self.params.desired_bits,
                    n_trailing_ones: 1,
                },
                &offset,
                &challenge,
                &self.params.hash,
            )?;
            hash.reduced.equal_when_carried_regroup(cs.namespace(|| "eq"), &allocated_expected_output)?;
            Ok(())
        }
    }

    circuit_tests! {
        hash_one_2048: (RsaHash {
            inputs: Some(
                        RsaHashInputs {
                            inputs: &[
                                "1",
                            ],
                        }
                    ),
                    params: RsaHashParams {
                        desired_bits: 2048,
                        limb_width: 32,
                        hash: Bn256PoseidonParams::new::<Keccak256Hasher>(),
                    }
        }, true),
        hash_ten_2048_bit_flip: (RsaHash {
            inputs: Some(
                        RsaHashInputs {
                            inputs: &[
                                "1", "2", "3", "4", "5", "6", "7", "8", "9", "9",
                            ],
                        }
                    ),
                    params: RsaHashParams {
                        desired_bits: 2048,
                        limb_width: 32,
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
                        limb_width: 32,
                        hash: Bn256PoseidonParams::new::<Keccak256Hasher>(),
                    }
        }, true),
    }
}
