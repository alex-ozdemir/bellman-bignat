use sapling_crypto::bellman::pairing::ff::{PrimeField, PrimeFieldRepr};
use sha2::{Digest, Sha256};

use std::cmp::min;
use std::iter::repeat;

pub fn bytes_to_bits(inputs: &[u8]) -> Vec<bool> {
    let mut v = Vec::new();
    for b in inputs {
        for i in 0..8 {
            v.push(((*b >> i) & 1) > 0);
        }
    }
    v
}

pub fn bits_to_bytes(inputs: &[bool]) -> Vec<u8> {
    let mut v = Vec::new();
    for slice in inputs.chunks(8) {
        let mut b = 0u8;
        for (i, bit) in slice.into_iter().enumerate() {
            b += (*bit as u8) << i;
        }
        v.push(b);
    }
    v
}

pub fn f_to_bits<F: PrimeField>(input: F) -> Vec<bool> {
    let mut bytes: Vec<u8> = Vec::new();
    input.into_repr().write_le(&mut bytes).unwrap();
    let mut bits = bytes_to_bits(&bytes);
    bits.truncate(F::NUM_BITS as usize);
    bits.extend(repeat(false).take(bits.len() - F::NUM_BITS as usize));
    bits
}

pub fn bits_to_f<F: PrimeField>(input: &[bool]) -> F {
    let bits = &input[..min(input.len(), F::CAPACITY as usize)];
    let bytes = bits_to_bytes(bits);
    let mut f = F::one().into_repr();
    f.read_le(bytes.as_slice()).unwrap();
    F::from_repr(f).unwrap()
}

/// Use the sha256 hash algorithm to digest these items
pub fn sha256<'a, F: PrimeField>(inputs: impl IntoIterator<Item = &'a F>) -> F {
    // First, we unpack
    let mut bits = inputs.into_iter().fold(Vec::new(), |mut v, f| {
        v.extend(f_to_bits(*f));
        v
    });
    bits.extend(repeat(false).take(((bits.len() - 1) / 8 + 1) * 8 - bits.len()));
    assert_eq!(bits.len() % 8, 0);
    println!("Comp input: {}", fmt_bits(bits.iter().copied()));
    let bytes = bits_to_bytes(&bits);
    let digest = Sha256::digest(&bytes);
    assert_eq!(digest.as_slice().len(), 32);
    let output_bits = bytes_to_bits(digest.as_slice());
    println!("Comp output: {}", fmt_bits(output_bits.iter().copied()));
    assert_eq!(output_bits.len(), 256);
    bits_to_f(&output_bits)
}

pub fn fmt_bits(bits: impl IntoIterator<Item = bool>) -> String {
    let mut s = String::new();
    use std::fmt::Write;
    for b in bits {
        write!(&mut s, "{}", if b { "1" } else { "0" }).unwrap();
    }
    s
}

pub mod circuit {
    use super::fmt_bits;
    use num_traits::One;
    use num_bigint::BigUint;
    use sapling_crypto::bellman::pairing::ff::{Field, PrimeField};
    use sapling_crypto::bellman::pairing::Engine;
    use sapling_crypto::bellman::ConstraintSystem;
    use sapling_crypto::circuit::boolean::Boolean;
    use sapling_crypto::circuit::num::AllocatedNum;
    use sapling_crypto::circuit::sha256::sha256 as sapling_sha256;

    use CResult;
    use OptionExt;
    use usize_to_f;
    use nat_to_f;

    use std::cmp::min;
    use std::iter::repeat;

    pub fn bools_to_num<E: Engine, CS: ConstraintSystem<E>>(
        mut cs: CS,
        input: &[Boolean],
    ) -> CResult<AllocatedNum<E>> {
        let bits = &input[..min(input.len(), <E::Fr as PrimeField>::CAPACITY as usize)];
        let num = AllocatedNum::alloc(cs.namespace(|| "num"), || {
            bits.iter().enumerate().try_fold(E::Fr::zero(), |mut acc, (i, b)| {
                let mut bit = usize_to_f::<E::Fr>(*b.get_value().grab()? as usize);
                bit.mul_assign(&nat_to_f(&(BigUint::one() << i)).expect("out-of-bounds scalar"));
                acc.add_assign(&bit);
                Ok(acc)
            })
        })?;
        cs.enforce(
            || "sum",
            |lc| lc,
            |lc| lc,
            |lc| bits.iter().enumerate().fold(lc - num.get_variable(), |acc, (i, b)| {
                acc + &b.lc(CS::one(), nat_to_f(&(BigUint::one() << i)).expect("out-of-bounds scalar"))
            }),
        );
        Ok(num)
    }

    pub fn sha256<E: Engine, CS: ConstraintSystem<E>>(
        mut cs: CS,
        inputs: &[AllocatedNum<E>],
    ) -> CResult<AllocatedNum<E>> {
        let mut bits = inputs
            .into_iter()
            .enumerate()
            .try_fold(Vec::new(), |mut v, (i, n)| -> CResult<Vec<Boolean>> {
                v.extend(n.into_bits_le_strict(cs.namespace(|| format!("bits {}", i)))?);
                Ok(v)
            })?;
        bits.extend(
            repeat(Boolean::constant(false)).take(((bits.len() - 1) / 8 + 1) * 8 - bits.len()),
        );
        println!("Circ input: {}", fmt_bits(bits.iter().map(|b| b.get_value().unwrap())));
        assert_eq!(bits.len() % 8, 0);
        let digest = sapling_sha256(cs.namespace(|| "sapling sha"), &bits)?;
        let flipped: Vec<Boolean> = digest
         .chunks(8)
         .map(|c| c.iter().rev())
         .flatten()
         .cloned()
         .collect();
        println!("Comp output: {}", fmt_bits(flipped.iter().map(|b| b.get_value().unwrap())));
        bools_to_num(cs.namespace(|| "to num"), &flipped)
    }
}
