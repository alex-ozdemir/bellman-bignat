use sapling_crypto::bellman::pairing::Engine;
use sapling_crypto::bellman::ConstraintSystem;
use sapling_crypto::circuit::num::AllocatedNum;

use util::bench::WitnessTimer;

/// Use the sha256 hash algorithm to digest these items
pub fn sha256<E: Engine>(inputs: &[E::Fr]) -> E::Fr {
    let mut cs = WitnessTimer::new();
    let nums: Vec<AllocatedNum<E>> = inputs
        .into_iter()
        .enumerate()
        .map(|(i, input)| {
            AllocatedNum::alloc(cs.namespace(|| format!("input {}", i)), || Ok(*input)).unwrap()
        })
        .collect();
    let output = circuit::sha256(cs.namespace(|| "sha"), &nums).unwrap();
    output.get_value().unwrap()
}

pub mod circuit {
    use num_bigint::BigUint;
    use num_traits::One;
    use sapling_crypto::bellman::pairing::ff::{Field, PrimeField};
    use sapling_crypto::bellman::pairing::Engine;
    use sapling_crypto::bellman::ConstraintSystem;
    use sapling_crypto::circuit::boolean::Boolean;
    use sapling_crypto::circuit::num::AllocatedNum;
    use sapling_crypto::circuit::sha256::sha256 as sapling_sha256;

    use util::convert::nat_to_f;
    use util::convert::usize_to_f;
    use CResult;
    use OptionExt;

    use std::cmp::min;
    use std::iter::repeat;

    pub fn bools_to_num<E: Engine, CS: ConstraintSystem<E>>(
        mut cs: CS,
        input: &[Boolean],
    ) -> CResult<AllocatedNum<E>> {
        let bits = &input[..min(input.len(), <E::Fr as PrimeField>::CAPACITY as usize)];
        let num = AllocatedNum::alloc(cs.namespace(|| "num"), || {
            bits.iter()
                .enumerate()
                .try_fold(E::Fr::zero(), |mut acc, (i, b)| {
                    let mut bit = usize_to_f::<E::Fr>(*b.get_value().grab()? as usize);
                    bit.mul_assign(
                        &nat_to_f(&(BigUint::one() << i)).expect("out-of-bounds scalar"),
                    );
                    acc.add_assign(&bit);
                    Ok(acc)
                })
        })?;
        cs.enforce(
            || "sum",
            |lc| lc,
            |lc| lc,
            |lc| {
                bits.iter()
                    .enumerate()
                    .fold(lc - num.get_variable(), |acc, (i, b)| {
                        acc + &b.lc(
                            CS::one(),
                            nat_to_f(&(BigUint::one() << i)).expect("out-of-bounds scalar"),
                        )
                    })
            },
        );
        Ok(num)
    }

    pub fn sha256<E: Engine, CS: ConstraintSystem<E>>(
        mut cs: CS,
        inputs: &[AllocatedNum<E>],
    ) -> CResult<AllocatedNum<E>> {
        let mut bits = inputs.into_iter().enumerate().try_fold(
            Vec::new(),
            |mut v, (i, n)| -> CResult<Vec<Boolean>> {
                v.extend(n.into_bits_le_strict(cs.namespace(|| format!("bits {}", i)))?);
                Ok(v)
            },
        )?;
        bits.extend(
            repeat(Boolean::constant(false)).take(((bits.len() - 1) / 8 + 1) * 8 - bits.len()),
        );
        assert_eq!(bits.len() % 8, 0);
        let digest = sapling_sha256(cs.namespace(|| "sapling sha"), &bits)?;
        bools_to_num(cs.namespace(|| "to num"), &digest)
    }
}
