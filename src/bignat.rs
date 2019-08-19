#![allow(dead_code)]
use bellman::{ConstraintSystem, LinearCombination, SynthesisError};
use ff::{Field, PrimeField};
use num_bigint::BigUint;
use num_traits::{Pow, ToPrimitive};
use std::cmp::max;
use std::rc::Rc;

use crate::bit::{Bit, Bitvector};
use crate::num::Num;
use crate::pairing::Engine;
use crate::poly::Polynomial;
use crate::OptionExt;
use crate::{f_to_nat, nat_to_f};

/// Compute the natural number represented by an array of limbs.
/// The limbs are assumed to be based the `limb_width` power of 2.
fn limbs_to_nat<'a, F: PrimeField, I: Iterator<Item = &'a F>>(
    limbs: I,
    limb_width: usize,
) -> BigUint {
    limbs
        .enumerate()
        .map(|(limb_i, limb)| (f_to_nat(limb) << (limb_i * limb_width)))
        .sum()
}

/// Compute the limbs encoding a natural number.
/// The limbs are assumed to be based the `limb_width` power of 2.
fn nat_to_limbs<'a, F: PrimeField>(nat: &BigUint, limb_width: usize, n_limbs: usize) -> Vec<F> {
    let mask = (BigUint::from(1usize) << limb_width) - 1usize;
    (0..n_limbs)
        .map(|limb_i| nat_to_f(&(&mask & (nat >> (limb_i * limb_width)))).unwrap())
        .collect()
}

/// A representation of a large natural number (a member of {0, 1, 2, ... })
#[derive(Clone)]
pub struct BigNat<E: Engine> {
    /// The linear combinations which constrain the value of each limb of the number
    limbs: Vec<LinearCombination<E>>,
    /// The witness values for each limb (filled at witness-time)
    limb_values: Option<Vec<E::Fr>>,
    /// The value of the whole number (filled at witness-time)
    value: Option<BigUint>,
    /// A circuit-time bound on the maximum value in all limbs
    max_word: BigUint,
    /// The number of bits in each limb (`2 ** limb_width` is the base)
    limb_width: usize,
}

impl<E: Engine> From<BigNat<E>> for Polynomial<E> {
    fn from(other: BigNat<E>) -> Polynomial<E> {
        Polynomial {
            coefficients: other.limbs,
            values: other.limb_values,
        }
    }
}

impl<E: Engine> BigNat<E> {
    /// Allocates a `BigNat` in the circuit with `n_limbs` limbs of width `limb_width` each.
    /// If `max_word` is missing, then it is assumed to be `(2 << limb_width) - 1`.
    /// The value is provided by a closure returning limb values.
    pub fn alloc_from_limbs<CS, F>(
        mut cs: CS,
        f: F,
        max_word: Option<BigUint>,
        limb_width: usize,
        n_limbs: usize,
    ) -> Result<Self, SynthesisError>
    where
        CS: ConstraintSystem<E>,
        F: FnOnce() -> Result<Vec<E::Fr>, SynthesisError>,
    {
        let values_cell = crate::lazy::LazyCell::new(f);
        let mut value = None;
        let mut limb_values = None;
        let limbs = (0..n_limbs)
            .map(|limb_i| {
                cs.alloc(
                    || format!("limb {}", limb_i),
                    || match *values_cell.borrow() {
                        Ok(ref vs) => {
                            if vs.len() != n_limbs {
                                return Err(SynthesisError::Unsatisfiable);
                            }
                            if value.is_none() {
                                value = Some(limbs_to_nat(vs.iter(), limb_width));
                            }
                            if limb_values.is_none() {
                                limb_values = Some(vs.clone());
                            }
                            Ok(vs[limb_i])
                        }
                        // Hack b/c SynthesisError and io::Error don't implement Clone
                        Err(ref e) => Err(SynthesisError::from(std::io::Error::new(
                            std::io::ErrorKind::Other,
                            format!("{}", e),
                        ))),
                    },
                )
                .map(|v| LinearCombination::zero() + v)
            })
            .collect::<Result<Vec<_>, _>>()?;
        Ok(Self {
            value,
            limb_values,
            limbs,
            max_word: max_word
                .unwrap_or_else(|| Pow::pow(&BigUint::from(2usize), limb_width) - 1usize),
            limb_width,
        })
    }

    /// Allocates a `BigNat` in the circuit with `n_limbs` limbs of width `limb_width` each.
    /// The `max_word` is gauranteed to be `(2 << limb_width) - 1`.
    /// The value is provided by a closure returning a natural number.
    pub fn alloc_from_nat<CS, F>(
        mut cs: CS,
        f: F,
        limb_width: usize,
        n_limbs: usize,
    ) -> Result<Self, SynthesisError>
    where
        CS: ConstraintSystem<E>,
        F: FnOnce() -> Result<BigUint, SynthesisError>,
    {
        let all_values_cell = crate::lazy::LazyCell::new(|| {
            f().map(|v| (nat_to_limbs::<E::Fr>(&v, limb_width, n_limbs), v))
                .map_err(Rc::new)
        });
        let mut value = None;
        let mut limb_values = Vec::new();
        let limbs = (0..n_limbs)
            .map(|limb_i| {
                cs.alloc(
                    || format!("limb {}", limb_i),
                    || match *all_values_cell.borrow() {
                        Ok((ref vs, ref v)) => {
                            if value.is_none() {
                                value = Some(v.clone());
                            }
                            limb_values.push(vs[limb_i]);
                            Ok(vs[limb_i])
                        }
                        // Hack b/c SynthesisError and io::Error don't implement Clone
                        Err(ref e) => Err(SynthesisError::from(std::io::Error::new(
                            std::io::ErrorKind::Other,
                            format!("{}", e),
                        ))),
                    },
                )
                .map(|v| LinearCombination::zero() + v)
            })
            .collect::<Result<Vec<_>, _>>()?;
        Ok(Self {
            value,
            limb_values: if limb_values.len() > 0 {
                Some(limb_values)
            } else {
                None
            },
            limbs,
            max_word: Pow::pow(&BigUint::from(2usize), limb_width) - 1usize,
            limb_width,
        })
    }

    /// Constrain `self` to be equal to `other`, assuming that they're both properly carried.
    pub fn equal<CS: ConstraintSystem<E>>(
        &self,
        mut cs: CS,
        other: &Self,
    ) -> Result<(), SynthesisError> {
        if self.limbs.len() != other.limbs.len() || self.limb_width != other.limb_width {
            return Err(SynthesisError::Unsatisfiable);
        }
        let n = self.limbs.len();
        for i in 0..n {
            cs.enforce(
                || format!("equal {}", i),
                |lc| lc,
                |lc| lc,
                |lc| lc + &self.limbs[i] - &other.limbs[i],
            );
        }
        Ok(())
    }

    /// Break `self` up into a bit-vector.
    fn decompose<CS: ConstraintSystem<E>>(
        &self,
        mut cs: CS,
    ) -> Result<Bitvector<E>, SynthesisError> {
        let limb_values_split =
            (0..self.limbs.len()).map(|i| self.limb_values.as_ref().map(|vs| vs[i]));
        let bitvectors: Vec<Bitvector<E>> = self
            .limbs
            .iter()
            .zip(limb_values_split)
            .enumerate()
            .map(|(i, (limb, limb_value))| {
                Num::new(limb_value, limb.clone())
                    .fits_in_bits(cs.namespace(|| format!("subdecmop {}", i)), self.limb_width)
            })
            .collect::<Result<Vec<_>, _>>()?;
        let mut bits = Vec::new();
        let mut values = Vec::new();
        for bv in bitvectors {
            bits.extend(bv.bits);
            bv.values.map(|vs| values.extend(vs));
        }
        let values = if values.len() > 0 { Some(values) } else { None };
        Ok(Bitvector { bits, values })
    }

    pub fn from_poly(poly: Polynomial<E>, limb_width: usize, max_word: BigUint) -> Self {
        Self {
            limbs: poly.coefficients,
            value: poly
                .values
                .as_ref()
                .map(|limb_values| limbs_to_nat(limb_values.iter(), limb_width)),
            max_word,
            limb_values: poly.values,
            limb_width,
        }
    }

    /// Constrain `self` to be equal to `other`, after carrying both.
    pub fn equal_when_carried<CS: ConstraintSystem<E>>(
        &self,
        mut cs: CS,
        other: &Self,
    ) -> Result<(), SynthesisError> {
        if self.limbs.len() != other.limbs.len() || self.limb_width != other.limb_width {
            return Err(SynthesisError::Unsatisfiable);
        }

        let n = self.limbs.len();
        let target_base = Pow::pow(&BigUint::from(2usize), self.limb_width);
        let mut accumulated_extra = BigUint::from(0usize);
        let max_word = std::cmp::max(&self.max_word, &other.max_word);
        let carry_bits = (((max_word.to_f64().unwrap() * 2.0).log2() - self.limb_width as f64)
            .ceil()
            + 0.1) as usize;
        let mut carry_in = Num::new(Some(E::Fr::zero()), LinearCombination::zero());

        for i in 0..n {
            let carry = Num::alloc(cs.namespace(|| format!("carry value {}", i)), || {
                Ok(nat_to_f(
                    &((f_to_nat(&self.limb_values.grab()?[i])
                        + f_to_nat(&carry_in.value.unwrap())
                        + max_word
                        - f_to_nat(&other.limb_values.grab()?[i]))
                        / &target_base),
                )
                .unwrap())
            })?;
            accumulated_extra += max_word;

            cs.enforce(
                || format!("carry {}", i),
                |lc| lc,
                |lc| lc,
                |lc| {
                    lc + &carry_in.num + &self.limbs[i] - &other.limbs[i]
                        + (nat_to_f(&max_word).unwrap(), CS::one())
                        - (nat_to_f(&target_base).unwrap(), &carry.num)
                        - (
                            nat_to_f(&(&accumulated_extra % &target_base)).unwrap(),
                            CS::one(),
                        )
                },
            );

            accumulated_extra /= &target_base;

            if i < n - 1 {
                carry.fits_in_bits(cs.namespace(|| format!("carry {} decomp", i)), carry_bits)?;
            } else {
                cs.enforce(
                    || format!("carry {} is out", i),
                    |lc| lc,
                    |lc| lc,
                    |lc| lc + &carry.num - (nat_to_f(&accumulated_extra).unwrap(), CS::one()),
                );
            }
            carry_in = Num::from(carry);
        }
        Ok(())
    }

    /// Constrain `self` to be equal to `other`, after carrying both.
    /// Uses regrouping internally to take full advantage of the field size and reduce the amount
    /// of carrying.
    pub fn equal_when_carried_regroup<CS: ConstraintSystem<E>>(
        &self,
        mut cs: CS,
        other: &Self,
    ) -> Result<(), SynthesisError> {
        if self.limbs.len() != other.limbs.len() || self.limb_width != other.limb_width {
            return Err(SynthesisError::Unsatisfiable);
        }
        let max_word = std::cmp::max(&self.max_word, &other.max_word);
        let carry_bits = (((max_word.to_f64().unwrap() * 2.0).log2() - self.limb_width as f64)
            .ceil()
            + 0.1) as usize;
        let limbs_per_group = (E::Fr::CAPACITY as usize - carry_bits) / self.limb_width;
        let self_grouped = self.regroup(limbs_per_group);
        let other_grouped = other.regroup(limbs_per_group);
        self_grouped.equal_when_carried(cs.namespace(|| "grouped"), &other_grouped)
    }

    /// Compute a `BigNat` contrained to be equal to `self * other % modulus`.
    pub fn mult_mod<CS: ConstraintSystem<E>>(
        &self,
        mut cs: CS,
        other: &Self,
        modulus: &Self,
    ) -> Result<(BigNat<E>, BigNat<E>), SynthesisError> {
        if self.limb_width != other.limb_width {
            return Err(SynthesisError::Unsatisfiable);
        }
        let limb_width = self.limb_width;
        let quotient_limbs = self.limbs.len() + other.limbs.len() - modulus.limbs.len();
        let quotient = BigNat::alloc_from_nat(
            cs.namespace(|| "quotient"),
            || Ok(self.value.grab()? * other.value.grab()? / modulus.value.grab()?),
            self.limb_width,
            quotient_limbs,
        )?;
        let remainder = BigNat::alloc_from_nat(
            cs.namespace(|| "remainder"),
            || Ok(self.value.grab()? * other.value.grab()? % modulus.value.grab()?),
            self.limb_width,
            modulus.limbs.len(),
        )?;
        let a_poly = Polynomial::from(self.clone());
        let b_poly = Polynomial::from(other.clone());
        let mod_poly = Polynomial::from(modulus.clone());
        let q_poly = Polynomial::from(BigNat::from(quotient.clone()));
        let r_poly = Polynomial::from(BigNat::from(remainder.clone()));

        // a * b
        let left = a_poly.alloc_product(cs.namespace(|| "left"), &b_poly)?;
        let right_product = q_poly.alloc_product(cs.namespace(|| "right_product"), &mod_poly)?;
        // q * m + r
        let right = Polynomial::from(right_product).sum(&r_poly);

        let left_max_word = BigUint::from(std::cmp::min(self.limbs.len(), other.limbs.len()))
            * &self.max_word
            * &other.max_word;
        let right_max_word =
            BigUint::from(std::cmp::min(quotient.limbs.len(), modulus.limbs.len()))
                * &quotient.max_word
                * &modulus.max_word
                + &remainder.max_word;

        let left_int = BigNat::from_poly(Polynomial::from(left), limb_width, left_max_word);
        let right_int = BigNat::from_poly(Polynomial::from(right), limb_width, right_max_word);
        left_int.equal_when_carried_regroup(cs.namespace(|| "carry"), &right_int)?;
        Ok((quotient, remainder))
    }

    /// Combines limbs into groups.
    pub fn regroup(&self, limbs_per_group: usize) -> BigNat<E> {
        let n_groups = (self.limbs.len() - 1) / limbs_per_group + 1;
        let limb_values = self.limb_values.as_ref().map(|vs| {
            let mut values: Vec<E::Fr> =
                std::iter::repeat_with(E::Fr::zero).take(n_groups).collect();
            for (i, v) in vs.iter().enumerate() {
                let mut b = E::Fr::from_str("2")
                    .unwrap()
                    .pow(&[((i % limbs_per_group) * self.limb_width) as u64]);
                b.mul_assign(&v);
                values[i / limbs_per_group].add_assign(&b);
            }
            values
        });
        let limbs = {
            let mut limbs: Vec<LinearCombination<E>> =
                std::iter::repeat_with(LinearCombination::zero)
                    .take(n_groups)
                    .collect();
            for (i, limb) in self.limbs.iter().enumerate() {
                let b = E::Fr::from_str("2")
                    .unwrap()
                    .pow(&[((i % limbs_per_group) * self.limb_width) as u64]);
                limbs[i / limbs_per_group] = limbs[i / limbs_per_group].clone() + (b, limb);
            }
            limbs
        };
        let max_word = (0..limbs_per_group)
            .map(|i| BigUint::from(2usize) << (i * self.limb_width))
            .sum::<BigUint>()
            * &self.max_word;
        BigNat {
            limb_width: self.limb_width,
            limbs,
            limb_values,
            value: self.value.clone(),
            max_word,
        }
    }

    /// Select `self` if `select` is false. Otherwise `other`.
    pub fn mux<CS: ConstraintSystem<E>>(
        &self,
        mut cs: CS,
        other: &Self,
        select: Bit<E>,
    ) -> Result<BigNat<E>, SynthesisError> {
        if self.limbs.len() != other.limbs.len() || self.limb_width != other.limb_width {
            return Err(SynthesisError::Unsatisfiable);
        }
        let value = select.value.and_then(|b| {
            if b {
                other.value.clone()
            } else {
                self.value.clone()
            }
        });
        let limb_values = select.value.and_then(|b| {
            if b {
                other.limb_values.clone()
            } else {
                self.limb_values.clone()
            }
        });
        let limbs: Vec<LinearCombination<E>> = self
            .limbs
            .iter()
            .zip(&other.limbs)
            .enumerate()
            .map(|(i, (self_l, other_l))| {
                let var = cs.alloc(|| format!("out {}", i), || Ok(limb_values.grab()?[i]))?;
                cs.enforce(
                    || format!("select {}", i),
                    |lc| lc + &select.bit,
                    |lc| lc + other_l - self_l,
                    |lc| lc + var - self_l,
                );
                Ok(LinearCombination::zero() + var)
            })
            .collect::<Result<Vec<LinearCombination<E>>, SynthesisError>>()?;
        Ok(Self {
            value,
            limb_values,
            limbs,
            limb_width: self.limb_width,
            max_word: max(&self.max_word, &other.max_word).clone(),
        })
    }

    /// NB: `exp` should have its bits *in reverse*. That is, the bit at index 0 is high order.
    pub fn pow_mod_bin_rev<CS: ConstraintSystem<E>>(
        &self,
        mut cs: CS,
        mut exp: Bitvector<E>,
        modulus: &Self,
    ) -> Result<BigNat<E>, SynthesisError> {
        if exp.bits.len() == 0 {
            Ok(BigNat {
                limb_values: Some({
                    let mut v = vec![E::Fr::one()];
                    for _ in 0..(self.limbs.len() - 1) {
                        v.push(E::Fr::zero())
                    }
                    v
                }),
                value: Some(BigUint::from(1usize)),
                limbs: {
                    let mut v = vec![LinearCombination::zero() + CS::one()];
                    for _ in 0..(self.limbs.len() - 1) {
                        v.push(LinearCombination::zero())
                    }
                    v
                },
                limb_width: self.limb_width,
                max_word: BigUint::from(1usize),
            })
        } else {
            let square = self.mult_mod(cs.namespace(|| "square"), &self, modulus)?.1;
            let select_bit = Bit {
                // Unwrap is safe b/c of `n_bits` check
                value: exp.values.as_mut().map(|vs| vs.pop().unwrap()),
                bit: exp.bits.pop().unwrap(),
            };
            let rec = square.pow_mod_bin_rev(cs.namespace(|| "rec"), exp, modulus)?;
            let prod = rec.mult_mod(cs.namespace(|| "prod"), &self, modulus)?.1;
            rec.mux(cs.namespace(|| "mux"), &prod, select_bit)
        }
    }

    /// Computes a `BigNat` constrained to be equal to `self ** exp % modulus`.
    pub fn pow_mod<CS: ConstraintSystem<E>>(
        &self,
        mut cs: CS,
        exp: &Self,
        modulus: &Self,
    ) -> Result<BigNat<E>, SynthesisError> {
        let exp_bin_rev = exp.decompose(cs.namespace(|| "exp decomp"))?.reversed();
        self.pow_mod_bin_rev(cs.namespace(|| "binary exp"), exp_bin_rev, modulus)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use bellman::Circuit;
    use pairing::bn256::Bn256;
    use quickcheck::TestResult;
    use sapling_crypto::circuit::test::TestConstraintSystem;

    use crate::usize_to_f;
    use std::str::FromStr;

    macro_rules! circuit_tests {
        ($($name:ident: $value:expr,)*) => {
            $(
                #[test]
                fn $name() {
                    let (circuit, is_sat) = $value;
                    let mut cs = TestConstraintSystem::<Bn256>::new();

                    circuit.synthesize(&mut cs).expect("synthesis failed");
                    println!(concat!("Constaints in {}: {}"), stringify!($name), cs.num_constraints());
                    if is_sat && !cs.is_satisfied() {
                        println!("UNSAT: {:#?}", cs.which_is_unsatisfied())
                    }

                    assert_eq!(cs.is_satisfied(), is_sat);
                }
            )*
        }
    }

    pub struct CarrierInputs {
        pub a: Vec<usize>,
        pub b: Vec<usize>,
    }

    pub struct CarrierParameters {
        pub max_word: usize,
        pub limb_width: usize,
        pub n_limbs: usize,
    }

    pub struct Carrier {
        inputs: Option<CarrierInputs>,
        params: CarrierParameters,
    }

    circuit_tests! {
        carry_2limbs_trivial: (Carrier {
            inputs: Some(CarrierInputs {
                a: vec![1,1],
                b: vec![1,1],
            }),
            params: CarrierParameters {
                max_word: 10,
                limb_width: 3,
                n_limbs: 2,
            }
        }, true),
        carry_4limbs_trivial: (Carrier {
            inputs: Some(CarrierInputs {
                a: vec![1,1,1,1],
                b: vec![1,1,1,1],
            }),
            params: CarrierParameters {
                max_word: 10,
                limb_width: 3,
                n_limbs: 4,
            }
        }, true),
        carry_4limbs_wrong_trivial: (Carrier {
            inputs: Some(CarrierInputs {
                a: vec![1,0,1,1],
                b: vec![1,1,1,1],
            }),
            params: CarrierParameters {
                max_word: 10,
                limb_width: 3,
                n_limbs: 4,
            }
        }, false),
        carry_4limbs_1carry: (Carrier {
            inputs: Some(CarrierInputs {
                a: vec![1,1,0,9],
                b: vec![1,1,1,1],
            }),
            params: CarrierParameters {
                max_word: 10,
                limb_width: 3,
                n_limbs: 4,
            }
        }, true),
        carry_4limbs_2carry: (Carrier {
            inputs: Some(CarrierInputs {
                a: vec![1,1,9,9],
                b: vec![1,2,2,1],
            }),
            params: CarrierParameters {
                max_word: 10,
                limb_width: 3,
                n_limbs: 4,
            }
        }, true),
        carry_4limbs_2carry_wrong: (Carrier {
            inputs: Some(CarrierInputs {
                a: vec![1,1,8,9],
                b: vec![1,2,2,1],
            }),
            params: CarrierParameters {
                max_word: 10,
                limb_width: 3,
                n_limbs: 4,
            }
        }, false),
    }

    impl<E: Engine> Circuit<E> for Carrier {
        fn synthesize<CS: ConstraintSystem<E>>(self, cs: &mut CS) -> Result<(), SynthesisError> {
            if let Some(a) = self.inputs.as_ref().map(|i| &i.a) {
                if a.len() != self.params.n_limbs {
                    return Err(SynthesisError::Unsatisfiable);
                }
            }
            if let Some(b) = self.inputs.as_ref().map(|i| &i.b) {
                if b.len() != self.params.n_limbs {
                    return Err(SynthesisError::Unsatisfiable);
                }
            }
            // Reverse the inputs so that the test cases can be written with digits in normal order
            let a = BigNat::alloc_from_limbs(
                cs.namespace(|| "a"),
                || {
                    Ok(self
                        .inputs
                        .as_ref()
                        .grab()?
                        .a
                        .iter()
                        .rev()
                        .copied()
                        .map(usize_to_f)
                        .collect())
                },
                Some(BigUint::from(self.params.max_word)),
                self.params.limb_width,
                self.params.n_limbs,
            )?;
            let b = BigNat::alloc_from_limbs(
                cs.namespace(|| "b"),
                || {
                    Ok(self
                        .inputs
                        .as_ref()
                        .grab()?
                        .b
                        .iter()
                        .rev()
                        .copied()
                        .map(usize_to_f)
                        .collect())
                },
                Some(BigUint::from(self.params.max_word)),
                self.params.limb_width,
                self.params.n_limbs,
            )?;
            a.equal_when_carried(cs.namespace(|| "carrier"), &b)?;
            a.equal_when_carried_regroup(cs.namespace(|| "carrier_regroup"), &b)?;
            Ok(())
        }
    }

    #[derive(Debug)]
    pub struct MultModInputs {
        pub a: BigUint,
        pub b: BigUint,
        pub m: BigUint,
        pub q: BigUint,
        pub r: BigUint,
    }

    pub struct MultModParameters {
        pub limb_width: usize,
        pub n_limbs_a: usize,
        pub n_limbs_b: usize,
        pub n_limbs_m: usize,
    }

    pub struct MultMod {
        inputs: Option<MultModInputs>,
        params: MultModParameters,
    }

    impl<E: Engine> Circuit<E> for MultMod {
        fn synthesize<CS: ConstraintSystem<E>>(self, cs: &mut CS) -> Result<(), SynthesisError> {
            let a = BigNat::alloc_from_nat(
                cs.namespace(|| "a"),
                || Ok(self.inputs.grab()?.a.clone()),
                self.params.limb_width,
                self.params.n_limbs_a,
            )?;
            let b = BigNat::alloc_from_nat(
                cs.namespace(|| "b"),
                || Ok(self.inputs.grab()?.b.clone()),
                self.params.limb_width,
                self.params.n_limbs_b,
            )?;
            let m = BigNat::alloc_from_nat(
                cs.namespace(|| "m"),
                || Ok(self.inputs.grab()?.m.clone()),
                self.params.limb_width,
                self.params.n_limbs_m,
            )?;
            let q = BigNat::alloc_from_nat(
                cs.namespace(|| "q"),
                || Ok(self.inputs.grab()?.q.clone()),
                self.params.limb_width,
                self.params.n_limbs_a + self.params.n_limbs_b - self.params.n_limbs_m,
            )?;
            let r = BigNat::alloc_from_nat(
                cs.namespace(|| "r"),
                || Ok(self.inputs.grab()?.r.clone()),
                self.params.limb_width,
                self.params.n_limbs_m,
            )?;
            let (qa, ra) = a.mult_mod(cs.namespace(|| "prod"), &b, &m)?;
            qa.equal(cs.namespace(|| "qcheck"), &q)?;
            ra.equal(cs.namespace(|| "rcheck"), &r)?;
            Ok(())
        }
    }

    circuit_tests! {
        mult_mod_1_by_1: ( MultMod {
            params: MultModParameters {
                limb_width: 4,
                n_limbs_a: 2,
                n_limbs_b: 2,
                n_limbs_m: 2,
            },
            inputs: Some(MultModInputs {
                a: BigUint::from(1usize),
                b: BigUint::from(1usize),
                m: BigUint::from(255usize),
                q: BigUint::from(0usize),
                r: BigUint::from(1usize),
            }),
        }, true),
        mult_mod_1_by_0: ( MultMod {
            params: MultModParameters {
                limb_width: 4,
                n_limbs_a: 2,
                n_limbs_b: 2,
                n_limbs_m: 2,
            },
            inputs: Some(MultModInputs {
                a: BigUint::from(1usize),
                b: BigUint::from(0usize),
                m: BigUint::from(255usize),
                q: BigUint::from(0usize),
                r: BigUint::from(0usize),
            }),
        }, true),
        mult_mod_2_by_2: ( MultMod {
            params: MultModParameters {
                limb_width: 4,
                n_limbs_a: 2,
                n_limbs_b: 2,
                n_limbs_m: 2,
            },
            inputs: Some(MultModInputs {
                a: BigUint::from(2usize),
                b: BigUint::from(2usize),
                m: BigUint::from(255usize),
                q: BigUint::from(0usize),
                r: BigUint::from(4usize),
            }),
        }, true),
        mult_mod_16_by_16: ( MultMod {
            params: MultModParameters {
                limb_width: 4,
                n_limbs_a: 2,
                n_limbs_b: 2,
                n_limbs_m: 2,
            },
            inputs: Some(MultModInputs {
                a: BigUint::from(16usize),
                b: BigUint::from(16usize),
                m: BigUint::from(255usize),
                q: BigUint::from(1usize),
                r: BigUint::from(1usize),
            }),
        }, true),
        mult_mod_254_by_254: ( MultMod {
            params: MultModParameters {
                limb_width: 4,
                n_limbs_a: 2,
                n_limbs_b: 2,
                n_limbs_m: 2,
            },
            inputs: Some(MultModInputs {
                a: BigUint::from(254usize),
                b: BigUint::from(254usize),
                m: BigUint::from(255usize),
                q: BigUint::from(253usize),
                r: BigUint::from(1usize),
            }),
        }, true),
        mult_mod_254_by_254_wrong: ( MultMod {
            params: MultModParameters {
                limb_width: 4,
                n_limbs_a: 2,
                n_limbs_b: 2,
                n_limbs_m: 2,
            },
            inputs: Some(MultModInputs {
                a: BigUint::from(254usize),
                b: BigUint::from(254usize),
                m: BigUint::from(255usize),
                q: BigUint::from(253usize),
                r: BigUint::from(0usize),
            }),
        }, false),
        mult_mod_110_by_180_mod187: ( MultMod {
            params: MultModParameters {
                limb_width: 4,
                n_limbs_a: 2,
                n_limbs_b: 2,
                n_limbs_m: 2,
            },
            inputs: Some(MultModInputs {
                a: BigUint::from(110usize),
                b: BigUint::from(180usize),
                m: BigUint::from(187usize),
                q: BigUint::from(105usize),
                r: BigUint::from(165usize),
            }),
        }, true),
        mult_mod_2w_by_6w: ( MultMod {
            params: MultModParameters {
                limb_width: 4,
                n_limbs_a: 6,
                n_limbs_b: 2,
                n_limbs_m: 2,
            },
            inputs: Some(MultModInputs {
                a: BigUint::from(16777215usize),
                b: BigUint::from(180usize),
                m: BigUint::from(255usize),
                q: BigUint::from(11842740usize),
                r: BigUint::from(0usize),
            }),
        }, true),
        mult_mod_2w_by_6w_test_2: ( MultMod {
            params: MultModParameters {
                limb_width: 4,
                n_limbs_a: 6,
                n_limbs_b: 2,
                n_limbs_m: 2,
            },
            inputs: Some(MultModInputs {
                a: BigUint::from(16777210usize),
                b: BigUint::from(180usize),
                m: BigUint::from(255usize),
                q: BigUint::from(11842736usize),
                r: BigUint::from(120usize),
            }),
        }, true),
    }

    #[derive(Debug)]
    pub struct NumberBitDecompInputs {
        pub n: BigUint,
    }

    pub struct NumberBitDecompParams {
        pub n_bits: usize,
    }

    pub struct NumberBitDecomp {
        inputs: Option<NumberBitDecompInputs>,
        params: NumberBitDecompParams,
    }

    impl<E: Engine> Circuit<E> for NumberBitDecomp {
        fn synthesize<CS: ConstraintSystem<E>>(self, cs: &mut CS) -> Result<(), SynthesisError> {
            let n = Num::alloc(cs.namespace(|| "n"), || {
                Ok(nat_to_f(&self.inputs.grab()?.n).unwrap())
            })?;
            n.fits_in_bits(cs.namespace(|| "decomp"), self.params.n_bits)?;
            Ok(())
        }
    }

    circuit_tests! {
        decomp_1_into_1b: (
            NumberBitDecomp {
                params: NumberBitDecompParams {
                    n_bits: 1,
                },
                inputs: Some(NumberBitDecompInputs {
                    n: BigUint::from(1usize),
                }),
            },
            true
        ),
        decomp_1_into_2b: (
            NumberBitDecomp {
                params: NumberBitDecompParams {
                    n_bits: 2,
                },
                inputs: Some(NumberBitDecompInputs {
                    n: BigUint::from(1usize),
                }),
            },
            true
        ),
        decomp_5_into_2b_fails: (
            NumberBitDecomp {
                params: NumberBitDecompParams {
                    n_bits: 2,
                },
                inputs: Some(NumberBitDecompInputs {
                    n: BigUint::from(5usize),
                }),
            },
            false
        ),
        decomp_255_into_8b: (
            NumberBitDecomp {
                params: NumberBitDecompParams {
                    n_bits: 8,
                },
                inputs: Some(NumberBitDecompInputs {
                    n: BigUint::from(255usize),
                }),
            },
            true
        ),
    }

    #[derive(Debug)]
    pub struct BigNatBitDecompInputs {
        pub n: BigUint,
    }

    pub struct BigNatBitDecompParams {
        pub limb_width: usize,
        pub n_limbs: usize,
    }

    pub struct BigNatBitDecomp {
        inputs: Option<BigNatBitDecompInputs>,
        params: BigNatBitDecompParams,
    }

    impl<E: Engine> Circuit<E> for BigNatBitDecomp {
        fn synthesize<CS: ConstraintSystem<E>>(self, cs: &mut CS) -> Result<(), SynthesisError> {
            let n = BigNat::alloc_from_nat(
                cs.namespace(|| "n"),
                || Ok(self.inputs.grab()?.n.clone()),
                self.params.limb_width,
                self.params.n_limbs,
            )?;
            n.decompose(cs.namespace(|| "decomp"))?;
            Ok(())
        }
    }

    #[quickcheck]
    fn big_nat_can_decompose(n: u32, limb_width: u8) -> TestResult {
        let n = n as usize;
        if limb_width < 4 || limb_width > 200 {
            return TestResult::discard();
        }
        let n_limbs = if n == 0 {
            1
        } else {
            (n - 1) / limb_width as usize + 1
        };

        let circuit = BigNatBitDecomp {
            inputs: Some(BigNatBitDecompInputs {
                n: BigUint::from(n),
            }),
            params: BigNatBitDecompParams {
                limb_width: limb_width as usize,
                n_limbs,
            },
        };
        let mut cs = TestConstraintSystem::<Bn256>::new();
        circuit.synthesize(&mut cs).expect("synthesis failed");
        TestResult::from_bool(cs.is_satisfied())
    }

    #[derive(Debug)]
    pub struct PowModInputs<'a> {
        pub b: &'a str,
        pub e: &'a str,
        pub m: &'a str,
        pub res: &'a str,
    }

    pub struct PowModParams {
        pub limb_width: usize,
        pub n_limbs_b: usize,
        pub n_limbs_e: usize,
    }

    pub struct PowMod<'a> {
        inputs: Option<PowModInputs<'a>>,
        params: PowModParams,
    }

    impl<'a, E: Engine> Circuit<E> for PowMod<'a> {
        fn synthesize<CS: ConstraintSystem<E>>(self, cs: &mut CS) -> Result<(), SynthesisError> {
            let b = BigNat::alloc_from_nat(
                cs.namespace(|| "b"),
                || Ok(BigUint::from_str(self.inputs.grab()?.b).unwrap()),
                self.params.limb_width,
                self.params.n_limbs_b,
            )?;
            let e = BigNat::alloc_from_nat(
                cs.namespace(|| "e"),
                || Ok(BigUint::from_str(self.inputs.grab()?.e).unwrap()),
                self.params.limb_width,
                self.params.n_limbs_e,
            )?;
            let res = BigNat::alloc_from_nat(
                cs.namespace(|| "res"),
                || Ok(BigUint::from_str(self.inputs.grab()?.res).unwrap()),
                self.params.limb_width,
                self.params.n_limbs_b,
            )?;
            let m = BigNat::alloc_from_nat(
                cs.namespace(|| "m"),
                || Ok(BigUint::from_str(self.inputs.grab()?.m).unwrap()),
                self.params.limb_width,
                self.params.n_limbs_b,
            )?;
            let actual = b.pow_mod(cs.namespace(|| "pow"), &e, &m)?;
            actual.equal(cs.namespace(|| "check"), &res)?;
            Ok(())
        }
    }

    circuit_tests! {
            pow_mod_1_to_0: (
                PowMod {
                    params: PowModParams {
                        limb_width: 4,
                        n_limbs_b: 2,
                        n_limbs_e: 2,
                    },
                    inputs: Some(PowModInputs {
                        b: "1",
                        e: "0",
                        m: "255",
                        res: "1",
                    }),
                },
                true
            ),
            pow_mod_1_to_1: (
                PowMod {
                    params: PowModParams {
                        limb_width: 4,
                        n_limbs_b: 2,
                        n_limbs_e: 2,
                    },
                    inputs: Some(PowModInputs {
                        b: "1",
                        e: "1",
                        m: "255",
                        res: "1",
                    }),
                },
                true
            ),
            pow_mod_1_to_255: (
                PowMod {
                    params: PowModParams {
                        limb_width: 4,
                        n_limbs_b: 2,
                        n_limbs_e: 2,
                    },
                    inputs: Some(PowModInputs {
                        b: "1",
                        e: "255",
                        m: "255",
                        res: "1",
                    }),
                },
                true
            ),
            pow_mod_2_to_2: (
                PowMod {
                    params: PowModParams {
                        limb_width: 4,
                        n_limbs_b: 3,
                        n_limbs_e: 1,
                    },
                    inputs: Some(PowModInputs {
                        b: "2",
                        e: "2",
                        m: "1255",
                        res: "4",
                    }),
                },
                true
            ),
            pow_mod_16_to_2: (
                PowMod {
                    params: PowModParams {
                        limb_width: 4,
                        n_limbs_b: 2,
                        n_limbs_e: 2,
                    },
                    inputs: Some(PowModInputs {
                        b: "16",
                        e: "2",
                        m: "255",
                        res: "1",
                    }),
                },
                true
            ),
            pow_mod_16_to_5: (
                PowMod {
                    params: PowModParams {
                        limb_width: 4,
                        n_limbs_b: 2,
                        n_limbs_e: 2,
                    },
                    inputs: Some(PowModInputs {
                        b: "16",
                        e: "5",
                        m: "255",
                        res: "16",
                    }),
                },
                true
            ),
            pow_mod_16_to_255: (
                PowMod {
                    params: PowModParams {
                        limb_width: 4,
                        n_limbs_b: 2,
                        n_limbs_e: 2,
                    },
                    inputs: Some(PowModInputs {
                        b: "16",
                        e: "254",
                        m: "255",
                        res: "1",
                    }),
                },
                true
            ),
    // This is a production-sized test. On my machine it takes
    // ~5GB and 30s.
    //        pow_mod_16_to_255_2048x128: (
    //            PowMod {
    //                params: PowModParams {
    //                    limb_width: 32,
    //                    n_limbs_b: 64,
    //                    n_limbs_e: 4,
    //                },
    //                inputs: Some(PowModInputs {
    //                    b: "16",
    //                    e: "254",
    //                    m: "255",
    //                    res: "1",
    //                }),
    //            },
    //            true
    //        ),
        }
}
