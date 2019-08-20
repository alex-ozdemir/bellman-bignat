use bellman::{ConstraintSystem, SynthesisError};
use num_bigint::BigUint;
use num_traits::One;
use pairing::Engine;

use bignat::BigNat;
use OptionExt;

pub fn proof_of_exp<E: Engine, CS: ConstraintSystem<E>>(
    mut cs: CS,
    base: BigNat<E>,
    modulus: BigNat<E>,
    power_factors: Vec<BigNat<E>>,
    result: BigNat<E>,
    challenge: BigNat<E>,
) -> Result<(), SynthesisError> {
    if base.limb_width != modulus.limb_width
        || base.limb_width != result.limb_width
        || base.limbs.len() != modulus.limbs.len()
        || base.limbs.len() != result.limbs.len()
    {
        return Err(SynthesisError::Unsatisfiable);
    }
    // \exists q s.t. q^l \times base^r = result
    // TODO (aozdemir) This computation is rather inefficient, because it handles very large
    let q_computation = || -> Result<BigUint, SynthesisError> {
        let mut prod = BigUint::one();
        for pow in &power_factors {
            prod *= pow.value.grab()?;
        }
        Ok(base
            .value
            .grab()?
            .modpow(&(prod / challenge.value.grab()?), modulus.value.grab()?))
    };
    let r_computation = || -> Result<BigUint, SynthesisError> {
        let mut prod = BigUint::one();
        let l = challenge.value.grab()?;
        for pow in &power_factors {
            if pow.limb_width != challenge.limb_width {
                return Err(SynthesisError::Unsatisfiable);
            }
            prod = prod * pow.value.grab()? % l;
        }
        Ok(prod)
    };
    let q = BigNat::alloc_from_nat(
        cs.namespace(|| "Q"),
        q_computation,
        base.limb_width,
        base.limbs.len(),
    )?;
    let r = BigNat::alloc_from_nat(
        cs.namespace(|| "Q"),
        r_computation,
        challenge.limb_width,
        challenge.limbs.len(),
    )?;
    let ql = q.pow_mod(cs.namespace(|| "Q^l"), &challenge, &modulus)?;
    let br = base.pow_mod(cs.namespace(|| "b^r"), &r, &modulus)?;
    let left = ql.mult_mod(cs.namespace(|| "Q^l b^r"), &br, &modulus)?.1;
    left.equal(cs.namespace(|| "Q^l b^r == res"), &result)
}
