use num_bigint::BigUint;
use sapling_crypto::bellman::pairing::ff::PrimeField;
use sapling_crypto::bellman::pairing::Engine;
use sapling_crypto::bellman::{ConstraintSystem, SynthesisError};
use sapling_crypto::circuit::boolean::Boolean;
use sapling_crypto::circuit::num::AllocatedNum;

use std::str::FromStr;

use super::circuit::{CircuitHasher, MaybeHashed};
use super::HashDomain;
use super::Hasher;
use mp::bignat::BigNat;
use util::bit::{Bit, Bitvector};
use wesolowski::Reduced;

// Chosen randomly.
const OFFSET_2048: &str = "30731438344250145947882657666206403727243332864808664054575262055190442942812700108124167942976653745028212341196692947492080562974589240558404052155436479139607283861572110186639866316589725954212169900473106847592072353357762907262662369230376196184226071545259316873351199416881666739376881925207433619609913435128355340248285568061176332195286623104126482371089555666194830543043595601648501184952472930075767818065617175977748228906417030406830990961578747315754348300610520710090878042950122953510395835606916522592211024941845938097013497415239566963754154588561352876059012472806373183052035005766579987123343";
const OFFSET_512: &str = "12260090376946711734120031891656796026361161089996129826004640183990021905572572824302484514470302046195674460977677239638547760386187660404531883140339307";
const OFFSET_128: &str = "320302797835264872593630364493262722277";

pub mod helper {
    use num_bigint::BigUint;
    use sapling_crypto::bellman::pairing::ff::PrimeField;

    use super::super::low_k_bits;
    use super::super::HashDomain;
    use super::super::Hasher;
    use util::convert::f_to_nat;

    pub fn di_hash<H: Hasher>(
        inputs: &[H::F],
        offset: &BigUint,
        domain: &HashDomain,
        limb_width: usize,
        hasher: &H,
    ) -> BigUint {
        let bits_per_hash = H::F::CAPACITY as usize;
        assert!(domain.n_bits % limb_width == 0);
        let hash = hasher.hash(inputs);
        let x = low_k_bits(&f_to_nat(&hash), bits_per_hash);
        offset + x
    }
}

pub fn offset(bit_width: usize) -> BigUint {
    BigUint::from_str(match bit_width {
        128 => OFFSET_128,
        512 => OFFSET_512,
        2048 => OFFSET_2048,
        n => panic!("Unsupported RSA bit_width: {}", n),
    })
    .unwrap()
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

pub fn di_hash<E, H, CS>(
    mut cs: CS,
    input: &mut MaybeHashed<E>,
    limb_width: usize,
    domain: &HashDomain,
    offset: Reduced<E>,
    hasher: &H,
) -> Result<BigNat<E>, SynthesisError>
where
    E: Engine,
    H: CircuitHasher<E = E> + Hasher<F = E::Fr>,
    CS: ConstraintSystem<E>,
{
    let bits_per_hash = H::F::CAPACITY as usize;
    assert!(domain.n_bits % limb_width == 0);
    let hash: AllocatedNum<E> =
        input.get_hash(|values| hasher.allocate_hash(cs.namespace(|| "inputs"), values))?;
    let hash_bits = hash.into_bits_le_strict(cs.namespace(|| "bitify"))?;
    let bits: Vec<Boolean> = hash_bits.into_iter().take(bits_per_hash).collect();
    let x = BigNat::<E>::recompose(
        &Bitvector::from_bits(
            bits.into_iter()
                .map(|b| Bit::from_sapling::<CS>(b))
                .collect(),
        ),
        limb_width,
    );
    x.add::<CS>(&offset.raw)
}

pub fn modded_di_hash<E, H, CS>(
    mut cs: CS,
    input: &mut MaybeHashed<E>,
    limb_width: usize,
    domain: &HashDomain,
    offset: &Reduced<E>,
    challenge: &BigNat<E>,
    hasher: &H,
) -> Result<Reduced<E>, SynthesisError>
where
    E: Engine,
    H: CircuitHasher<E = E> + Hasher<F = E::Fr>,
    CS: ConstraintSystem<E>,
{
    let bits_per_hash = H::F::CAPACITY as usize;
    assert!(domain.n_bits % limb_width == 0);
    let hash: AllocatedNum<E> =
        input.get_hash(|values| hasher.allocate_hash(cs.namespace(|| "inputs"), values))?;
    let hash_bits = hash.into_bits_le_strict(cs.namespace(|| "bitify"))?;
    let bits: Vec<Boolean> = hash_bits.into_iter().take(bits_per_hash).collect();
    let x = BigNat::<E>::recompose(
        &Bitvector::from_bits(
            bits.into_iter()
                .map(|b| Bit::from_sapling::<CS>(b))
                .collect(),
        ),
        limb_width,
    );
    let r = x
        .add::<CS>(&offset.reduced)?
        .red_mod(cs.namespace(|| "x % l"), challenge)?;
    Ok(Reduced {
        raw: offset.raw.add::<CS>(&x)?,
        reduced: r,
    })
}

#[cfg(test)]
mod test {
    use super::*;

    use num_bigint::BigUint;
    use sapling_crypto::bellman::pairing::ff::PrimeField;
    use sapling_crypto::bellman::{ConstraintSystem, SynthesisError};
    use sapling_crypto::circuit::num::AllocatedNum;

    use std::str::FromStr;

    use super::super::circuit::CircuitHasher;
    use super::super::hashes::Poseidon;
    use hash::Hasher;
    use mp::bignat::BigNat;
    use util::test_helpers::*;
    use OptionExt;

    pub struct RsaHashInputs<'a> {
        pub inputs: &'a [&'a str],
    }

    pub struct RsaHashParams<H> {
        pub desired_bits: usize,
        pub limb_width: usize,
        pub hasher: H,
    }

    pub struct RsaHash<'a, H> {
        inputs: Option<RsaHashInputs<'a>>,
        params: RsaHashParams<H>,
    }

    impl<'a, E: Engine, H: Hasher<F = E::Fr> + CircuitHasher<E = E>> Circuit<E> for RsaHash<'a, H> {
        fn synthesize<CS: ConstraintSystem<E>>(self, cs: &mut CS) -> Result<(), SynthesisError> {
            let input_values: Vec<E::Fr> = self
                .inputs
                .grab()?
                .inputs
                .iter()
                .map(|s| E::Fr::from_str(s).unwrap())
                .collect();
            let cv =
                BigUint::from_str("5104102027859293093184735748236254201176269103281996090807")
                    .unwrap();
            let challenge =
                BigNat::alloc_from_nat(cs.namespace(|| "challenge"), || Ok(cv.clone()), 32, 6)?;
            let offset = super::allocate_offset(cs.namespace(|| "offset"), &challenge, 2048)?;
            let expected_ouput = super::helper::di_hash(
                &input_values,
                offset.raw.value.as_ref().unwrap(),
                &HashDomain {
                    n_bits: self.params.desired_bits,
                    n_trailing_ones: 1,
                },
                self.params.limb_width,
                &self.params.hasher,
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
            let mut hashed = MaybeHashed::from_values(allocated_inputs);
            let hash = super::modded_di_hash(
                cs.namespace(|| "hash"),
                &mut hashed,
                32,
                &HashDomain {
                    n_bits: self.params.desired_bits,
                    n_trailing_ones: 1,
                },
                &offset,
                &challenge,
                &self.params.hasher,
            )?;
            hash.reduced
                .equal_when_carried_regroup(cs.namespace(|| "eq"), &allocated_expected_output)?;
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
                        hasher: Poseidon::default(),
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
                        hasher: Poseidon::default(),
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
                        hasher: Poseidon::default(),
                    }
        }, true),
    }
}
