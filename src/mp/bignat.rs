use rug::Integer;
use sapling_crypto::bellman::pairing::ff::{Field, PrimeField};
use sapling_crypto::bellman::pairing::Engine;
use sapling_crypto::bellman::{ConstraintSystem, LinearCombination, SynthesisError};
use sapling_crypto::circuit::boolean::Boolean;

use std::borrow::Borrow;
use std::cmp::{max, min, Ordering};
use std::convert::From;
use std::fmt::{self, Debug, Display, Formatter};
use std::rc::Rc;

use super::exp::optimal_k;
use super::poly::Polynomial;
use util::bit::{Bit, Bitvector};
use util::convert::{f_to_nat, nat_to_f};
use util::gadget::Gadget;
use util::lazy::LazyCell;
use util::num::Num;
use OptionExt;

/// Compute the natural number represented by an array of limbs.
/// The limbs are assumed to be based the `limb_width` power of 2.
pub fn limbs_to_nat<F: PrimeField, B: Borrow<F>, I: DoubleEndedIterator<Item = B>>(
    limbs: I,
    limb_width: usize,
) -> Integer {
    limbs.rev().fold(Integer::from(0), |mut acc, limb| {
        acc <<= limb_width as u32;
        acc += f_to_nat(limb.borrow());
        acc
    })
}

fn int_with_n_ones(n: usize) -> Integer {
    let mut m = Integer::from(1);
    m <<= n as u32;
    m -= 1;
    m
}

/// Compute the limbs encoding a natural number.
/// The limbs are assumed to be based the `limb_width` power of 2.
pub fn nat_to_limbs<'a, F: PrimeField>(
    nat: &Integer,
    limb_width: usize,
    n_limbs: usize,
) -> Result<Vec<F>, SynthesisError> {
    let mask = int_with_n_ones(limb_width);
    let mut nat = nat.clone();
    if nat.significant_bits() as usize <= n_limbs * limb_width {
        Ok((0..n_limbs)
            .map(|_| {
                let r = Integer::from(&nat & &mask);
                nat >>= limb_width as u32;
                nat_to_f(&r).unwrap()
            })
            .collect())
    } else {
        eprintln!(
            "nat {} does not fit in {} limbs of width {}",
            nat, n_limbs, limb_width
        );
        Err(SynthesisError::Unsatisfiable)
    }
}

#[derive(Clone, PartialEq, Eq)]
pub struct BigNatParams {
    pub min_bits: usize,
    pub max_word: Integer,
    pub limb_width: usize,
    pub n_limbs: usize,
}

impl BigNatParams {
    pub fn new(limb_width: usize, n_limbs: usize) -> Self {
        let mut max_word = Integer::from(1) << limb_width as u32;
        max_word -= 1;
        BigNatParams {
            max_word,
            n_limbs,
            limb_width,
            min_bits: 0,
        }
    }
}

/// A representation of a large natural number (a member of {0, 1, 2, ... })
#[derive(Clone)]
pub struct BigNat<E: Engine> {
    /// The linear combinations which constrain the value of each limb of the number
    pub limbs: Vec<LinearCombination<E>>,
    /// The witness values for each limb (filled at witness-time)
    pub limb_values: Option<Vec<E::Fr>>,
    /// The value of the whole number (filled at witness-time)
    pub value: Option<Integer>,
    /// Parameters
    pub params: BigNatParams,
}

impl<E: Engine> std::cmp::PartialEq for BigNat<E> {
    fn eq(&self, other: &Self) -> bool {
        self.value == other.value && self.params == other.params
    }
}
impl<E: Engine> std::cmp::Eq for BigNat<E> {}

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
        max_word: Option<Integer>,
        limb_width: usize,
        n_limbs: usize,
    ) -> Result<Self, SynthesisError>
    where
        CS: ConstraintSystem<E>,
        F: FnOnce() -> Result<Vec<E::Fr>, SynthesisError>,
    {
        let values_cell = LazyCell::new(f);
        let mut value = None;
        let mut limb_values = None;
        let limbs = (0..n_limbs)
            .map(|limb_i| {
                cs.alloc(
                    || format!("limb {}", limb_i),
                    || match *values_cell.borrow() {
                        Ok(ref vs) => {
                            if vs.len() != n_limbs {
                                eprintln!("Values do not match stated limb count");
                                return Err(SynthesisError::Unsatisfiable);
                            }
                            if value.is_none() {
                                value = Some(limbs_to_nat::<E::Fr, _, _>(vs.iter(), limb_width));
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
            params: BigNatParams {
                min_bits: 0,
                n_limbs,
                max_word: max_word.unwrap_or_else(|| int_with_n_ones(limb_width)),
                limb_width,
            },
        })
    }

    /// Creates a `BigNat` in the circuit from the given limbs.
    pub fn from_limbs(limbs: Vec<Num<E>>, limb_width: usize) -> Self {
        let limb_values = limbs
            .iter()
            .map(|n| n.value)
            .collect::<Option<Vec<E::Fr>>>();
        let value = limb_values
            .as_ref()
            .map(|values| limbs_to_nat::<E::Fr, _, _>(values.iter(), limb_width));
        let max_word = int_with_n_ones(limb_width);
        Self {
            params: BigNatParams {
                min_bits: 0,
                n_limbs: limbs.len(),
                max_word,
                limb_width,
            },
            value,
            limb_values,
            limbs: limbs
                .into_iter()
                .map(|i| LinearCombination::zero() + &i.num)
                .collect(),
        }
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
        F: FnOnce() -> Result<Integer, SynthesisError>,
    {
        let all_values_cell = LazyCell::new(|| {
            f().and_then(|v| Ok((nat_to_limbs::<E::Fr>(&v, limb_width, n_limbs)?, v)))
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
            params: BigNatParams::new(limb_width, n_limbs),
        })
    }

    pub fn from_num(n: Num<E>, params: BigNatParams) -> Self {
        Self {
            value: n.value.as_ref().map(|n| f_to_nat(n)),
            limb_values: n.value.map(|v| vec![v]),
            limbs: vec![n.num],
            params,
        }
    }

    pub fn as_limbs<CS: ConstraintSystem<E>>(&self) -> Vec<Num<E>> {
        let mut limbs = Vec::new();
        for (i, lc) in self.limbs.iter().enumerate() {
            limbs.push(Num::new(
                self.limb_values.as_ref().map(|vs| vs[i].clone()),
                lc.clone(),
            ));
        }
        limbs
    }

    pub fn inputize<CS: ConstraintSystem<E>>(&self, mut cs: CS) -> Result<(), SynthesisError> {
        for (i, l) in self.limbs.iter().enumerate() {
            let mut c = cs.namespace(|| format!("limb {}", i));
            let v = c.alloc_input(|| "alloc", || Ok(self.limb_values.as_ref().grab()?[i]))?;
            c.enforce(|| "eq", |lc| lc, |lc| lc, |lc| lc + v - l);
        }
        Ok(())
    }

    /// Constrain `self` to be equal to `other`, assuming that they're both properly carried.
    pub fn equal<CS: ConstraintSystem<E>>(
        &self,
        mut cs: CS,
        other: &Self,
    ) -> Result<(), SynthesisError> {
        if self.limbs.len() < other.limbs.len() {
            return other.equal(cs, self);
        }
        self.enforce_limb_width_agreement(other, "equal")?;
        let n = other.limbs.len();
        for i in 0..n {
            cs.enforce(
                || format!("equal {}", i),
                |lc| lc,
                |lc| lc,
                |lc| lc + &self.limbs[i] - &other.limbs[i],
            );
        }
        for i in n..(self.limbs.len()) {
            cs.enforce(
                || format!("equal {}", i),
                |lc| lc,
                |lc| lc,
                |lc| lc + &self.limbs[i],
            );
        }
        Ok(())
    }

    pub fn is_equal<CS: ConstraintSystem<E>>(
        &self,
        mut cs: CS,
        other: &Self,
    ) -> Result<Boolean, SynthesisError> {
        use sapling_crypto::circuit::num::{AllocatedNum, Num};
        let mut rolling = Boolean::Constant(true);
        if self.limbs.len() != other.limbs.len() {
            eprintln!(
                "Self has {} limbs, other {} (BigNat::is_equal)",
                self.limbs.len(),
                other.limbs.len()
            );
            return Err(SynthesisError::Unsatisfiable);
        }
        self.enforce_limb_width_agreement(other, "is_equal")?;
        let n = self.limbs.len();
        for i in 0..n {
            let self_limb = AllocatedNum::alloc(cs.namespace(|| format!("self {}", i)), || {
                Ok(self.limb_values.as_ref().grab()?[i])
            })?;
            cs.enforce(
                || format!("equal self {}", i),
                |lc| lc,
                |lc| lc,
                |lc| lc - &Num::from(self_limb.clone()).lc(E::Fr::one()) + &self.limbs[i],
            );
            let other_limb = AllocatedNum::alloc(cs.namespace(|| format!("other {}", i)), || {
                Ok(other.limb_values.as_ref().grab()?[i])
            })?;
            cs.enforce(
                || format!("equal other {}", i),
                |lc| lc,
                |lc| lc,
                |lc| lc - &Num::from(other_limb.clone()).lc(E::Fr::one()) + &other.limbs[i],
            );
            let b = AllocatedNum::equals(
                cs.namespace(|| format!("eq {}", i)),
                &self_limb,
                &other_limb,
            )?;
            rolling = Boolean::and(cs.namespace(|| format!("and {}", i)), &b, &rolling)?;
        }
        Ok(rolling)
    }

    pub fn assert_well_formed<CS: ConstraintSystem<E>>(
        &self,
        mut cs: CS,
    ) -> Result<(), SynthesisError> {
        // swap the option and iterator
        let limb_values_split =
            (0..self.limbs.len()).map(|i| self.limb_values.as_ref().map(|vs| vs[i]));
        for (i, (limb, limb_value)) in self.limbs.iter().zip(limb_values_split).enumerate() {
            Num::new(limb_value, limb.clone())
                .fits_in_bits(cs.namespace(|| format!("{}", i)), self.params.limb_width)?;
        }
        Ok(())
    }

    /// Break `self` up into a bit-vector.
    pub fn decompose<CS: ConstraintSystem<E>>(
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
                Num::new(limb_value, limb.clone()).decompose(
                    cs.namespace(|| format!("subdecmop {}", i)),
                    self.params.limb_width,
                )
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

    pub fn recompose(bv: &Bitvector<E>, limb_width: usize) -> Self {
        let nat = BigNat::from_limbs(
            bv.bits
                .iter()
                .enumerate()
                .map(|(i, bit)| {
                    let val =
                        bv.values
                            .as_ref()
                            .map(|v| if v[i] { E::Fr::one() } else { E::Fr::zero() });
                    Num::new(val, bit.clone())
                })
                .collect(),
            1,
        );
        nat.group_limbs(limb_width)
    }

    pub fn enforce_full_bits<CS: ConstraintSystem<E>>(
        &mut self,
        mut cs: CS,
    ) -> Result<(), SynthesisError> {
        let value = self
            .limb_values
            .as_ref()
            .map(|vs| vs.last().unwrap().clone());
        let lc = self.limbs.last().unwrap().clone();
        Num::new(value, lc)
            .decompose(cs.namespace(|| "decomp"), self.params.limb_width)?
            .into_bits()
            .last()
            .unwrap()
            .constrain_value(cs.namespace(|| "1"), true);
        self.params.min_bits = self.params.limb_width * self.params.n_limbs;
        Ok(())
    }

    pub fn enforce_min_bits<CS: ConstraintSystem<E>>(
        &mut self,
        mut cs: CS,
        min_bits: usize,
    ) -> Result<(), SynthesisError> {
        let bits = self.decompose(cs.namespace(|| "decomp"))?.into_bits();
        let upper_bits: Vec<Bit<E>> = bits.into_iter().skip(min_bits - 1).collect();
        let inverse = cs.alloc(
            || "inverse",
            || {
                Ok({
                    let mut sum = E::Fr::zero();
                    for b in &upper_bits {
                        if *b.value.grab()? {
                            sum.add_assign(&E::Fr::one());
                        }
                    }
                    sum.inverse();
                    sum
                })
            },
        )?;
        cs.enforce(
            || "inverse exists",
            |lc| lc + inverse,
            |lc| {
                let mut sum = lc;
                for b in &upper_bits {
                    sum = sum + &b.bit;
                }
                sum
            },
            |lc| lc + CS::one(),
        );
        self.params.min_bits = min_bits;
        Ok(())
    }

    pub fn enforce_limb_width_agreement(
        &self,
        other: &Self,
        location: &str,
    ) -> Result<usize, SynthesisError> {
        if self.params.limb_width == other.params.limb_width {
            return Ok(self.params.limb_width);
        } else {
            eprintln!(
                "Limb widths {}, {}, do not agree at {}",
                self.params.limb_width, other.params.limb_width, location
            );
            return Err(SynthesisError::Unsatisfiable);
        }
    }

    /// Concatenate two numbers. `self` becomes the high-order part.
    pub fn concat(&self, other: &Self) -> Result<Self, SynthesisError> {
        let limb_width = self.enforce_limb_width_agreement(other, "concat")?;
        let min_bits = if self.params.min_bits > 0 {
            self.params.min_bits + other.params.limb_width * other.params.n_limbs
        } else {
            other.params.min_bits
        };
        let mut limbs = other.limbs.clone();
        limbs.extend(self.limbs.iter().cloned());
        let mut limb_values = other.limb_values.clone();
        limb_values.as_mut().map(|x| {
            self.limb_values
                .as_ref()
                .map(|y| x.extend(y.iter().cloned()))
        });
        let value = self.value.clone().and_then(|sv| {
            other
                .value
                .as_ref()
                .map(|ov| (sv << (other.params.limb_width * other.params.n_limbs) as u32) + ov)
        });
        Ok(Self {
            params: BigNatParams {
                min_bits,
                max_word: max(&self.params.max_word, &other.params.max_word).clone(),
                n_limbs: self.params.n_limbs + other.params.n_limbs,
                limb_width,
            },
            limb_values,
            limbs,
            value,
        })
    }

    /// Produces the natural number with the low-order `n_limbs` of `self`.
    pub fn truncate_limbs(&self, n_limbs: usize) -> Self {
        let mut new = self.clone();
        if n_limbs < new.limbs.len() {
            while new.limbs.len() > n_limbs {
                new.limbs.pop();
                if let Some(limb_value) = new.limb_values.as_mut().map(|lvs| lvs.pop().unwrap()) {
                    *new.value.as_mut().unwrap() -=
                        f_to_nat(&limb_value) << (new.limbs.len() * new.params.limb_width) as u32;
                }
            }
            new.params.n_limbs = n_limbs;
            if new.params.min_bits > new.params.n_limbs * new.params.limb_width {
                new.params.min_bits = 0;
            }
        }
        new
    }

    pub fn from_poly(poly: Polynomial<E>, limb_width: usize, max_word: Integer) -> Self {
        Self {
            params: BigNatParams {
                min_bits: 0,
                max_word,
                n_limbs: poly.coefficients.len(),
                limb_width,
            },
            limbs: poly.coefficients,
            value: poly
                .values
                .as_ref()
                .map(|limb_values| limbs_to_nat::<E::Fr, _, _>(limb_values.iter(), limb_width)),
            limb_values: poly.values,
        }
    }

    /// Constrain `self` to be equal to `other`, after carrying both.
    pub fn equal_when_carried<CS: ConstraintSystem<E>>(
        &self,
        mut cs: CS,
        other: &Self,
    ) -> Result<(), SynthesisError> {
        self.enforce_limb_width_agreement(other, "equal_when_carried")?;

        // We'll propegate carries over the first `n` limbs.
        let n = min(self.limbs.len(), other.limbs.len());
        let target_base = Integer::from(1) << self.params.limb_width as u32;
        let mut accumulated_extra = Integer::from(0usize);
        let max_word = std::cmp::max(&self.params.max_word, &other.params.max_word);
        let carry_bits = (((max_word.to_f64() * 2.0).log2() - self.params.limb_width as f64).ceil()
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
                            nat_to_f(&Integer::from(&accumulated_extra % &target_base)).unwrap(),
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

        for (i, zero_limb) in self.limbs.iter().enumerate().skip(n) {
            cs.enforce(
                || format!("zero self {}", i),
                |lc| lc,
                |lc| lc,
                |lc| lc + zero_limb,
            );
        }
        for (i, zero_limb) in other.limbs.iter().enumerate().skip(n) {
            cs.enforce(
                || format!("zero other {}", i),
                |lc| lc,
                |lc| lc,
                |lc| lc + zero_limb,
            );
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
        self.enforce_limb_width_agreement(other, "equal_when_carried_regroup")?;
        let max_word = std::cmp::max(&self.params.max_word, &other.params.max_word);
        let carry_bits = (((max_word.to_f64() * 2.0).log2() - self.params.limb_width as f64).ceil()
            + 0.1) as usize;
        let limbs_per_group = (E::Fr::CAPACITY as usize - carry_bits) / self.params.limb_width;
        let self_grouped = self.group_limbs(limbs_per_group);
        let other_grouped = other.group_limbs(limbs_per_group);
        self_grouped.equal_when_carried(cs.namespace(|| "grouped"), &other_grouped)
    }

    // Constrain `self` to divide `other`.
    pub fn divides<CS: ConstraintSystem<E>>(
        &self,
        mut cs: CS,
        other: &Self,
    ) -> Result<(), SynthesisError> {
        self.enforce_limb_width_agreement(other, "divides")?;
        let factor = BigNat::alloc_from_nat(
            cs.namespace(|| "product"),
            || {
                let s = self.value.grab()?;
                let o = other.value.grab()?;
                if o.is_divisible(s) {
                    Ok(Integer::from(o / s))
                } else {
                    eprintln!("Not divisible");
                    Err(SynthesisError::Unsatisfiable)
                }
            },
            other.params.limb_width,
            other.params.n_limbs,
        )?;
        // Verify that factor is in bounds
        factor.assert_well_formed(cs.namespace(|| "rangecheck"))?;
        self.verify_mult(cs.namespace(|| "multcheck"), &factor, &other)
    }

    pub fn shift<CS: ConstraintSystem<E>>(&self, constant: E::Fr) -> BigNat<E> {
        assert!(self.limbs.len() > 0);
        let mut new = self.clone();
        assert!(new.limbs.len() > 0);
        new.limbs[0] =
            std::mem::replace(&mut new.limbs[0], LinearCombination::zero()) + (constant, CS::one());
        if let Some(vs) = new.limb_values.as_mut() {
            vs[0].add_assign(&constant);
        }
        if let Some(v) = new.value.as_mut() {
            *v += f_to_nat(&constant);
        }
        new.params.max_word += f_to_nat(&constant);
        assert!(new.params.max_word <= (Integer::from(1) << E::Fr::CAPACITY));
        new
    }

    pub fn scale<CS: ConstraintSystem<E>>(&self, constant: E::Fr) -> BigNat<E> {
        let mut new = self.clone();
        for limb in &mut new.limbs {
            *limb = LinearCombination::zero() + (constant, &*limb);
        }
        if let Some(vs) = new.limb_values.as_mut() {
            for v in vs {
                v.mul_assign(&constant);
            }
        }
        if let Some(v) = new.value.as_mut() {
            *v *= f_to_nat(&constant);
        }
        new.params.max_word *= f_to_nat(&constant);
        assert!(new.params.max_word <= (Integer::from(1) << E::Fr::CAPACITY));
        new
    }

    pub fn sub<CS: ConstraintSystem<E>>(
        &self,
        mut cs: CS,
        other: &Self,
    ) -> Result<BigNat<E>, SynthesisError> {
        let diff = BigNat::alloc_from_nat(
            cs.namespace(|| "diff"),
            || {
                let mut s = self.value.grab()?.clone();
                s -= other.value.grab()?;
                Ok(s)
            },
            self.params.limb_width,
            self.params.n_limbs,
        )?;
        let sum = other.add::<CS>(&diff)?;
        self.equal_when_carried_regroup(cs.namespace(|| "eq"), &sum)?;
        Ok(diff)
    }

    pub fn mult<CS: ConstraintSystem<E>>(
        &self,
        mut cs: CS,
        other: &Self,
    ) -> Result<BigNat<E>, SynthesisError> {
        self.enforce_limb_width_agreement(other, "mult")?;

        let mut prod = BigNat::alloc_from_nat(
            cs.namespace(|| "product"),
            || {
                let mut s = self.value.grab()?.clone();
                s *= other.value.grab()?;
                Ok(s)
            },
            other.params.limb_width,
            other.params.n_limbs + self.params.n_limbs,
        )?;
        if self.params.min_bits > 0 && other.params.min_bits > 0 {
            prod.params.min_bits = self.params.min_bits + other.params.min_bits - 1;
        }

        prod.assert_well_formed(cs.namespace(|| "rangecheck"))?;

        // Verify that factor is in bounds
        self.verify_mult(cs.namespace(|| "multcheck"), &other, &prod)?;
        Ok(prod)
    }

    pub fn add<CS: ConstraintSystem<E>>(&self, other: &Self) -> Result<BigNat<E>, SynthesisError> {
        self.enforce_limb_width_agreement(other, "add")?;
        let n_limbs = max(self.params.n_limbs, other.params.n_limbs);
        let max_word = Integer::from(&self.params.max_word + &other.params.max_word);
        let limbs: Vec<LinearCombination<E>> = (0..n_limbs)
            .map(|i| match (self.limbs.get(i), other.limbs.get(i)) {
                (Some(a), Some(b)) => a.clone() + b,
                (Some(a), None) => a.clone(),
                (None, Some(b)) => b.clone(),
                (None, None) => unreachable!(),
            })
            .collect();
        let limb_values: Option<Vec<E::Fr>> = self.limb_values.as_ref().and_then(|x| {
            other.limb_values.as_ref().map(|y| {
                (0..n_limbs)
                    .map(|i| match (x.get(i), y.get(i)) {
                        (Some(a), Some(b)) => {
                            let mut t = a.clone();
                            t.add_assign(b);
                            t
                        }
                        (Some(a), None) => a.clone(),
                        (None, Some(a)) => a.clone(),
                        (None, None) => unreachable!(),
                    })
                    .collect()
            })
        });
        let value = self
            .value
            .as_ref()
            .and_then(|x| other.value.as_ref().map(|y| Integer::from(x + y)));
        Ok(Self {
            limb_values,
            value,
            limbs,
            params: BigNatParams {
                min_bits: max(self.params.min_bits, other.params.min_bits),
                n_limbs,
                max_word,
                limb_width: self.params.limb_width,
            },
        })
    }

    pub fn min<CS: ConstraintSystem<E>>(
        &self,
        mut cs: CS,
        other: &Self,
    ) -> Result<Self, SynthesisError> {
        let select = Bit::alloc(
            cs.namespace(|| "select"),
            self.value
                .as_ref()
                .and_then(|s| other.value.as_ref().map(|o| o < s)),
        )?;
        let (lesser, greater) = Gadget::switch(cs.namespace(|| "switch"), &select, self, other)?;
        let _diff = greater.sub(cs.namespace(|| "difference"), other)?;
        Ok(lesser)
    }

    fn verify_mult<CS: ConstraintSystem<E>>(
        &self,
        mut cs: CS,
        other: &Self,
        prod: &Self,
    ) -> Result<(), SynthesisError> {
        self.enforce_limb_width_agreement(other, "verify_mult, other")?;
        self.enforce_limb_width_agreement(prod, "verify_mult, prod")?;
        // Verify that factor is in bounds
        let max_word = {
            let mut x = Integer::from(min(self.params.n_limbs, other.params.n_limbs));
            x *= &self.params.max_word;
            x *= &other.params.max_word;
            x
        };
        let poly_prod = Polynomial::from(self.clone()).alloc_product(
            cs.namespace(|| "poly product"),
            &Polynomial::from(other.clone()),
        )?;
        BigNat::from_poly(poly_prod, other.params.limb_width, max_word)
            .equal_when_carried_regroup(cs.namespace(|| "equal"), prod)?;
        Ok(())
    }

    pub fn enforce_coprime<CS: ConstraintSystem<E>>(
        &self,
        cs: CS,
        other: &Self,
    ) -> Result<(), SynthesisError> {
        let one = Self::one::<CS>(other.params.limb_width);
        self.enforce_gcd(cs, other, &one)
    }

    fn enforce_gcd<CS: ConstraintSystem<E>>(
        &self,
        mut cs: CS,
        other: &Self,
        gcd: &Self,
    ) -> Result<(), SynthesisError> {
        // What to multipy x by to get the gcd, mod y
        let self_pseudo_inverse = BigNat::alloc(
            cs.namespace(|| "x pseudo inverse"),
            self.value
                .as_ref()
                .and_then(|a| {
                    // To compute the bezout coefficients, we do some acrobatics b/c they might be
                    // negative
                    other
                        .value
                        .as_ref()
                        .map(|b| (a.clone().gcd_cofactors(b.clone(), Integer::new()).1 + b) % b)
                })
                .as_ref(),
            (),
            &other.params,
        )?;
        self_pseudo_inverse.assert_well_formed(cs.namespace(|| "pseudo inverse rangecheck"))?;
        self.assert_product_mod(
            cs.namespace(|| "lower bound"),
            &self_pseudo_inverse,
            other,
            &gcd,
        )?;
        gcd.divides(cs.namespace(|| "div a"), self)?;
        gcd.divides(cs.namespace(|| "div b"), &other)?;
        Ok(())
    }

    pub fn gcd<CS: ConstraintSystem<E>>(
        &self,
        mut cs: CS,
        other: &Self,
    ) -> Result<BigNat<E>, SynthesisError> {
        self.enforce_limb_width_agreement(other, "gcd")?;
        let limb_width = self.params.limb_width;
        let n_limbs = min(self.params.n_limbs, other.params.n_limbs);
        let gcd = BigNat::alloc(
            cs.namespace(|| "gcd"),
            self.value
                .as_ref()
                .and_then(|a| other.value.as_ref().map(|b| Integer::from(a.gcd_ref(b))))
                .as_ref(),
            (),
            &BigNatParams {
                min_bits: 1,
                max_word: int_with_n_ones(limb_width),
                n_limbs,
                limb_width,
            },
        )?;
        gcd.assert_well_formed(cs.namespace(|| "gcd rangecheck"))?;
        self.enforce_gcd(cs.namespace(|| "enforce"), other, &gcd)?;
        Ok(gcd)
    }

    pub fn assert_product_mod<CS: ConstraintSystem<E>>(
        &self,
        mut cs: CS,
        other: &Self,
        modulus: &Self,
        remainder: &Self,
    ) -> Result<BigNat<E>, SynthesisError> {
        self.enforce_limb_width_agreement(other, "assert_product_mod, other")?;
        self.enforce_limb_width_agreement(modulus, "assert_product_mod, modulus")?;
        self.enforce_limb_width_agreement(remainder, "assert_product_mod, remainder")?;
        let limb_width = self.params.limb_width;
        let quotient_limbs = self.limbs.len() + other.limbs.len();
        let quotient = BigNat::alloc_from_nat(
            cs.namespace(|| "quotient"),
            || {
                Ok({
                    let mut x: Integer = self.value.grab()?.clone();
                    x *= *other.value().grab()?;
                    x /= *modulus.value().grab()?;
                    x
                })
            },
            self.params.limb_width,
            quotient_limbs,
        )?;
        quotient.assert_well_formed(cs.namespace(|| "quotient rangecheck"))?;
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

        let left_max_word = {
            let mut x = Integer::from(min(self.limbs.len(), other.limbs.len()));
            x *= &self.params.max_word;
            x *= &other.params.max_word;
            x
        };
        let right_max_word = {
            let mut x = Integer::from(std::cmp::min(quotient.limbs.len(), modulus.limbs.len()));
            x *= &quotient.params.max_word;
            x *= &modulus.params.max_word;
            x += &remainder.params.max_word;
            x
        };

        let left_int = BigNat::from_poly(Polynomial::from(left), limb_width, left_max_word);
        let right_int = BigNat::from_poly(Polynomial::from(right), limb_width, right_max_word);
        left_int.equal_when_carried_regroup(cs.namespace(|| "carry"), &right_int)?;
        Ok(quotient)
    }

    /// Compute a `BigNat` contrained to be equal to `self * other % modulus`.
    pub fn mult_mod<CS: ConstraintSystem<E>>(
        &self,
        mut cs: CS,
        other: &Self,
        modulus: &Self,
    ) -> Result<(BigNat<E>, BigNat<E>), SynthesisError> {
        self.enforce_limb_width_agreement(other, "mult_mod")?;
        let limb_width = self.params.limb_width;
        let quotient_bits =
            (self.n_bits() + other.n_bits()).saturating_sub(modulus.params.min_bits);
        let quotient_limbs = quotient_bits.saturating_sub(1) / limb_width + 1;
        let quotient = BigNat::alloc_from_nat(
            cs.namespace(|| "quotient"),
            || {
                Ok({
                    let mut x = self.value.grab()?.clone();
                    x *= other.value.grab()?;
                    x /= modulus.value.grab()?;
                    x
                })
            },
            self.params.limb_width,
            quotient_limbs,
        )?;
        quotient.assert_well_formed(cs.namespace(|| "quotient rangecheck"))?;
        let remainder = BigNat::alloc_from_nat(
            cs.namespace(|| "remainder"),
            || {
                Ok({
                    let mut x = self.value.grab()?.clone();
                    x *= other.value.grab()?;
                    x %= modulus.value.grab()?;
                    x
                })
            },
            self.params.limb_width,
            modulus.limbs.len(),
        )?;
        remainder.assert_well_formed(cs.namespace(|| "remainder rangecheck"))?;
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

        let left_max_word = {
            let mut x = Integer::from(min(self.limbs.len(), other.limbs.len()));
            x *= &self.params.max_word;
            x *= &other.params.max_word;
            x
        };
        let right_max_word = {
            let mut x = Integer::from(std::cmp::min(quotient.limbs.len(), modulus.limbs.len()));
            x *= &quotient.params.max_word;
            x *= &modulus.params.max_word;
            x += &remainder.params.max_word;
            x
        };

        let left_int = BigNat::from_poly(Polynomial::from(left), limb_width, left_max_word);
        let right_int = BigNat::from_poly(Polynomial::from(right), limb_width, right_max_word);
        left_int.equal_when_carried_regroup(cs.namespace(|| "carry"), &right_int)?;
        Ok((quotient, remainder))
    }

    /// Compute a `BigNat` contrained to be equal to `self * other % modulus`.
    pub fn red_mod<CS: ConstraintSystem<E>>(
        &self,
        mut cs: CS,
        modulus: &Self,
    ) -> Result<BigNat<E>, SynthesisError> {
        self.enforce_limb_width_agreement(modulus, "red_mod")?;
        let limb_width = self.params.limb_width;
        let quotient_bits = self.n_bits().saturating_sub(modulus.params.min_bits);
        let quotient_limbs = quotient_bits.saturating_sub(1) / limb_width + 1;
        let quotient = BigNat::alloc_from_nat(
            cs.namespace(|| "quotient"),
            || Ok(Integer::from(self.value.grab()? / modulus.value.grab()?)),
            self.params.limb_width,
            quotient_limbs,
        )?;
        quotient.assert_well_formed(cs.namespace(|| "quotient rangecheck"))?;
        let remainder = BigNat::alloc_from_nat(
            cs.namespace(|| "remainder"),
            || Ok(Integer::from(self.value.grab()? % modulus.value.grab()?)),
            self.params.limb_width,
            modulus.limbs.len(),
        )?;
        remainder.assert_well_formed(cs.namespace(|| "remainder rangecheck"))?;
        let mod_poly = Polynomial::from(modulus.clone());
        let q_poly = Polynomial::from(BigNat::from(quotient.clone()));
        let r_poly = Polynomial::from(BigNat::from(remainder.clone()));

        // q * m + r
        let right_product = q_poly.alloc_product(cs.namespace(|| "right_product"), &mod_poly)?;
        let right = Polynomial::from(right_product).sum(&r_poly);

        let right_max_word = {
            let mut x = Integer::from(std::cmp::min(quotient.limbs.len(), modulus.limbs.len()));
            x *= &quotient.params.max_word;
            x *= &modulus.params.max_word;
            x += &remainder.params.max_word;
            x
        };

        let right_int = BigNat::from_poly(Polynomial::from(right), limb_width, right_max_word);
        self.equal_when_carried_regroup(cs.namespace(|| "carry"), &right_int)?;
        Ok(remainder)
    }

    /// Combines limbs into groups.
    pub fn group_limbs(&self, limbs_per_group: usize) -> BigNat<E> {
        let n_groups = (self.limbs.len() - 1) / limbs_per_group + 1;
        let limb_values = self.limb_values.as_ref().map(|vs| {
            let mut values: Vec<E::Fr> = vec![E::Fr::zero(); n_groups];
            let mut shift = E::Fr::one();
            let limb_block = (0..self.params.limb_width).fold(E::Fr::one(), |mut l, _| {
                l.double();
                l
            });
            for (i, v) in vs.iter().enumerate() {
                if i % limbs_per_group == 0 {
                    shift = E::Fr::one();
                }
                let mut a = shift.clone();
                a.mul_assign(&v);
                values[i / limbs_per_group].add_assign(&a);
                shift.mul_assign(&limb_block);
            }
            values
        });
        let limbs = {
            let mut limbs: Vec<LinearCombination<E>> = vec![LinearCombination::zero(); n_groups];
            let mut shift = E::Fr::one();
            let limb_block = (0..self.params.limb_width).fold(E::Fr::one(), |mut l, _| {
                l.double();
                l
            });
            for (i, limb) in self.limbs.iter().enumerate() {
                if i % limbs_per_group == 0 {
                    shift = E::Fr::one();
                }
                limbs[i / limbs_per_group] =
                    std::mem::replace(&mut limbs[i / limbs_per_group], LinearCombination::zero())
                        + (shift.clone(), limb);
                shift.mul_assign(&limb_block);
            }
            limbs
        };
        let max_word = (0..limbs_per_group).fold(Integer::from(0), |mut acc, i| {
            acc.set_bit((i * self.params.limb_width) as u32, true);
            acc
        }) * &self.params.max_word;
        BigNat {
            params: BigNatParams {
                min_bits: self.params.min_bits,
                limb_width: self.params.limb_width * limbs_per_group,
                n_limbs: limbs.len(),
                max_word,
            },
            limbs,
            limb_values,
            value: self.value.clone(),
        }
    }

    // NB: `exp` should have its bits *in reverse*. That is, the bit at index 0 is high order.
    fn pow_mod_bin_rev<CS: ConstraintSystem<E>>(
        &self,
        mut cs: CS,
        exp: Bitvector<E>,
        modulus: &Self,
    ) -> Result<BigNat<E>, SynthesisError> {
        fn bauer_power_bin_rev_helper<'a, E: Engine, CS: ConstraintSystem<E>>(
            mut cs: CS,
            base_powers: &[BigNat<E>],
            k: usize,
            mut exp_chunks: std::slice::Chunks<'a, Bit<E>>,
            modulus: &BigNat<E>,
        ) -> Result<BigNat<E>, SynthesisError> {
            if let Some(chunk) = exp_chunks.next_back() {
                let chunk_len = chunk.len();

                if exp_chunks.len() > 0 {
                    let mut acc = bauer_power_bin_rev_helper(
                        cs.namespace(|| "rec"),
                        base_powers,
                        k,
                        exp_chunks,
                        modulus,
                    )?;
                    // Square once, for each bit in the chunk
                    for j in 0..chunk_len {
                        acc = acc
                            .mult_mod(cs.namespace(|| format!("square {}", j)), &acc, &modulus)?
                            .1;
                    }
                    // Select the correct base power
                    let base_power = Gadget::mux_tree(
                        cs.namespace(|| "select"),
                        chunk.into_iter(),
                        &base_powers[..(1 << chunk_len)],
                    )?;
                    Ok(acc
                        .mult_mod(cs.namespace(|| "prod"), &base_power, &modulus)?
                        .1)
                } else {
                    Gadget::mux_tree(
                        cs.namespace(|| "select"),
                        chunk.into_iter(),
                        &base_powers[..(1 << chunk_len)],
                    )
                }
            } else {
                Ok(BigNat::one::<CS>(modulus.params.limb_width))
            }
        }
        let k = optimal_k(exp.bits.len());
        let base_powers = {
            let mut base_powers = vec![BigNat::one::<CS>(modulus.params.limb_width), self.clone()];
            for i in 2..(1 << k) {
                base_powers.push(
                    base_powers
                        .last()
                        .unwrap()
                        .mult_mod(cs.namespace(|| format!("base {}", i)), self, modulus)?
                        .1,
                );
            }
            base_powers
        };
        bauer_power_bin_rev_helper(
            cs.namespace(|| "helper"),
            &base_powers,
            k,
            exp.into_bits().chunks(k),
            modulus,
        )
    }

    /// Computes a `BigNat` constrained to be equal to `self ** exp % modulus`.
    pub fn pow_mod<CS: ConstraintSystem<E>>(
        &self,
        mut cs: CS,
        exp: &Self,
        modulus: &Self,
    ) -> Result<BigNat<E>, SynthesisError> {
        let exp_bin_rev = if exp.params.max_word >= Integer::from(1) << exp.params.limb_width as u32
        {
            let exp_carried = BigNat::alloc_from_nat(
                cs.namespace(|| "exp carried"),
                || Ok(exp.value.grab()?.clone()),
                exp.params.limb_width,
                exp.params.n_limbs,
            )?;
            exp_carried.equal_when_carried_regroup(cs.namespace(|| "carry check"), &exp)?;
            exp_carried
                .decompose(cs.namespace(|| "exp decomp"))?
                .reversed()
        } else {
            exp.decompose(cs.namespace(|| "exp decomp"))?.reversed()
        };
        self.pow_mod_bin_rev(cs.namespace(|| "binary exp"), exp_bin_rev, modulus)
    }

    /// Assuming that the input is equivalent to 3 modulo 4, does a round of Miller-Rabin to check
    /// for primality
    fn miller_rabin_round<CS: ConstraintSystem<E>>(
        &self,
        mut cs: CS,
        base: &Self,
    ) -> Result<Boolean, SynthesisError> {
        let bits = self.decompose(cs.namespace(|| "decomp"))?;
        if bits.bits.len() < 3 {
            eprintln!("Miller-Rabin too short");
            return Err(SynthesisError::Unsatisfiable);
        }
        // Unwraps are safe b/c of len check above
        bits.get(0)
            .unwrap()
            .constrain_value(cs.namespace(|| "odd"), true);
        bits.get(1)
            .unwrap()
            .constrain_value(cs.namespace(|| "= 3 mod 4"), true);
        let n_less_one = BigNat::recompose(&bits.clone().shr(1).shl(1), self.params.limb_width);
        let one = BigNat::alloc_from_nat(
            cs.namespace(|| "1"),
            || Ok(Integer::from(1)),
            self.params.limb_width,
            self.limbs.len(),
        )?;
        // 2a + 1 == n
        let a = BigNat::recompose(&bits.shr(1), self.params.limb_width);
        // Check that b^a == 1 (mod self) OR
        //            b^a == -1 (mod self)
        let pow = base.pow_mod(cs.namespace(|| "b^a"), &a, self)?;
        let is_1 = pow.is_equal(cs.namespace(|| "=1"), &n_less_one)?;
        let is_neg_1 = pow.is_equal(cs.namespace(|| "=-1"), &one)?;
        Ok(Boolean::and(cs.namespace(|| "or"), &is_1.not(), &is_neg_1.not())?.not())
    }

    fn miller_rabin_rounds<CS: ConstraintSystem<E>>(
        &self,
        mut cs: CS,
        bases: &[usize],
    ) -> Result<Boolean, SynthesisError> {
        let mut rolling = Boolean::Constant(true);
        for p in bases {
            let big_p = Integer::from(*p);
            if big_p.significant_bits() as usize > self.params.limb_width * self.limbs.len() {
                eprintln!("miller_rabin_rounds");
                return Err(SynthesisError::Unsatisfiable);
            }
            let base = BigNat::alloc_from_nat(
                cs.namespace(|| format!("base {}", p)),
                || Ok(big_p),
                self.params.limb_width,
                self.limbs.len(),
            )?;
            let round =
                self.miller_rabin_round(cs.namespace(|| format!("mr round with {}", p)), &base)?;
            rolling = Boolean::and(cs.namespace(|| format!("and {}", p)), &rolling, &round)?;
        }
        Ok(rolling)
    }

    pub fn with_n_limbs<CS: ConstraintSystem<E>>(&self, n_limbs: usize) -> Self {
        match n_limbs.cmp(&self.params.n_limbs) {
            Ordering::Less => panic!("Tried to downsize the number of limbs!"),
            Ordering::Equal => self.clone(),
            Ordering::Greater => {
                let mut new = self.clone();
                new.params.n_limbs = n_limbs;
                new.limb_values.as_mut().map(|vs| {
                    while vs.len() < n_limbs {
                        vs.push(E::Fr::zero())
                    }
                });
                while new.limbs.len() < n_limbs {
                    new.limbs.push(LinearCombination::zero())
                }
                new
            }
        }
    }

    pub fn one<CS: ConstraintSystem<E>>(limb_width: usize) -> Self {
        BigNat {
            limb_values: Some(vec![E::Fr::one()]),
            value: Some(Integer::from(1)),
            limbs: { vec![LinearCombination::zero() + CS::one()] },
            params: BigNatParams {
                min_bits: 1,
                n_limbs: 1,
                limb_width: limb_width,
                max_word: Integer::from(1),
            },
        }
    }

    pub fn miller_rabin<CS: ConstraintSystem<E>>(
        &self,
        cs: CS,
        n_rounds: usize,
    ) -> Result<Boolean, SynthesisError> {
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
        let ps = primes(n_rounds);
        self.miller_rabin_rounds(cs, &ps)
    }

    pub fn miller_rabin_32b<CS: ConstraintSystem<E>>(
        &self,
        cs: CS,
    ) -> Result<Boolean, SynthesisError> {
        self.miller_rabin_rounds(cs, &[2, 7, 61])
    }

    pub fn n_bits(&self) -> usize {
        assert!(self.params.n_limbs > 0);
        self.params.limb_width * (self.params.n_limbs - 1)
            + self.params.max_word.significant_bits() as usize
    }
}

impl<E: Engine> Gadget for BigNat<E> {
    type E = E;
    type Value = Integer;
    type Params = BigNatParams;
    type Access = ();
    fn alloc<CS: ConstraintSystem<E>>(
        cs: CS,
        value: Option<&Self::Value>,
        _access: (),
        params: &Self::Params,
    ) -> Result<Self, SynthesisError> {
        BigNat::alloc_from_nat(
            cs,
            || Ok((*value.grab()?).clone()),
            params.limb_width,
            params.n_limbs,
        )
    }
    fn value(&self) -> Option<&Integer> {
        self.value.as_ref()
    }
    fn wire_values(&self) -> Option<Vec<E::Fr>> {
        self.limb_values.clone()
    }
    fn params(&self) -> &BigNatParams {
        &self.params
    }
    fn wires(&self) -> Vec<LinearCombination<E>> {
        self.limbs.clone()
    }
    fn access(&self) -> &() {
        &()
    }
    fn mux<CS: ConstraintSystem<E>>(
        mut cs: CS,
        s: &Bit<E>,
        i0: &Self,
        i1: &Self,
    ) -> Result<Self, SynthesisError> {
        let n_limbs = max(i0.params.n_limbs, i1.params.n_limbs);
        let i0 = i0.with_n_limbs::<CS>(n_limbs);
        let i1 = i1.with_n_limbs::<CS>(n_limbs);
        let i0_wires = i0.wires();
        let i1_wires = i1.wires();
        if i0_wires.len() != i1_wires.len() || i0.params.limb_width != i1.params.limb_width {
            eprintln!("Wire mis-match in BigNat mux");
            return Err(SynthesisError::Unsatisfiable);
        }
        let value: Option<&Self::Value> = s
            .value
            .and_then(|b| if b { i1.value() } else { i0.value() });
        let out: Self = Self::alloc(
            cs.namespace(|| "out"),
            value,
            (),
            &BigNatParams {
                min_bits: min(i0.params.min_bits, i1.params.min_bits),
                max_word: max(i0.params.max_word.clone(), i1.params.max_word.clone()),
                limb_width: i0.params.limb_width,
                n_limbs: i0.params.n_limbs,
            },
        )?;
        let out_wires = out.wires();
        for (i, ((i0w, i1w), out_w)) in i0_wires
            .into_iter()
            .zip(i1_wires)
            .zip(out_wires)
            .enumerate()
        {
            cs.enforce(
                || format!("{}", i),
                |lc| lc + &s.bit,
                |lc| lc + &i1w - &i0w,
                |lc| lc + &out_w - &i0w,
            );
        }
        Ok(out)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use util::test_helpers::*;

    use quickcheck::TestResult;

    use std::str::FromStr;
    use util::convert::usize_to_f;

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
                    eprintln!("Unsat: inputs/n_limbs mismatch a");
                    return Err(SynthesisError::Unsatisfiable);
                }
            }
            if let Some(b) = self.inputs.as_ref().map(|i| &i.b) {
                if b.len() != self.params.n_limbs {
                    eprintln!("Unsat: inputs/n_limbs mismatch b");
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
                Some(Integer::from(self.params.max_word)),
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
                Some(Integer::from(self.params.max_word)),
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
        pub a: Integer,
        pub b: Integer,
        pub m: Integer,
        pub q: Integer,
        pub r: Integer,
    }

    pub struct MultModParameters {
        pub limb_width: usize,
        pub n_limbs_a: usize,
        pub n_limbs_b: usize,
        pub n_limbs_m: usize,
        pub full_m: bool,
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
            let mut m = BigNat::alloc_from_nat(
                cs.namespace(|| "m"),
                || Ok(self.inputs.grab()?.m.clone()),
                self.params.limb_width,
                self.params.n_limbs_m,
            )?;
            if self.params.full_m {
                m.enforce_full_bits(cs.namespace(|| "m is full"))?;
            }
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
                full_m: true,
            },
            inputs: Some(MultModInputs {
                a: Integer::from(1usize),
                b: Integer::from(1usize),
                m: Integer::from(255usize),
                q: Integer::from(0usize),
                r: Integer::from(1usize),
            }),
        }, true),
        mult_mod_1_by_0: ( MultMod {
            params: MultModParameters {
                limb_width: 4,
                n_limbs_a: 2,
                n_limbs_b: 2,
                n_limbs_m: 2,
                full_m: true,
            },
            inputs: Some(MultModInputs {
                a: Integer::from(1usize),
                b: Integer::from(0usize),
                m: Integer::from(255usize),
                q: Integer::from(0usize),
                r: Integer::from(0usize),
            }),
        }, true),
        mult_mod_2_by_2: ( MultMod {
            params: MultModParameters {
                limb_width: 4,
                n_limbs_a: 2,
                n_limbs_b: 2,
                n_limbs_m: 2,
                full_m: true,
            },
            inputs: Some(MultModInputs {
                a: Integer::from(2usize),
                b: Integer::from(2usize),
                m: Integer::from(255usize),
                q: Integer::from(0usize),
                r: Integer::from(4usize),
            }),
        }, true),
        mult_mod_16_by_16: ( MultMod {
            params: MultModParameters {
                limb_width: 4,
                n_limbs_a: 2,
                n_limbs_b: 2,
                n_limbs_m: 2,
                full_m: true,
            },
            inputs: Some(MultModInputs {
                a: Integer::from(16usize),
                b: Integer::from(16usize),
                m: Integer::from(255usize),
                q: Integer::from(1usize),
                r: Integer::from(1usize),
            }),
        }, true),
        mult_mod_254_by_254: ( MultMod {
            params: MultModParameters {
                limb_width: 4,
                n_limbs_a: 2,
                n_limbs_b: 2,
                n_limbs_m: 2,
                full_m: true,
            },
            inputs: Some(MultModInputs {
                a: Integer::from(254usize),
                b: Integer::from(254usize),
                m: Integer::from(255usize),
                q: Integer::from(253usize),
                r: Integer::from(1usize),
            }),
        }, true),
        mult_mod_254_by_254_wrong: ( MultMod {
            params: MultModParameters {
                limb_width: 4,
                n_limbs_a: 2,
                n_limbs_b: 2,
                n_limbs_m: 2,
                full_m: true,
            },
            inputs: Some(MultModInputs {
                a: Integer::from(254usize),
                b: Integer::from(254usize),
                m: Integer::from(255usize),
                q: Integer::from(253usize),
                r: Integer::from(0usize),
            }),
        }, false),
        mult_mod_110_by_180_mod187: ( MultMod {
            params: MultModParameters {
                limb_width: 4,
                n_limbs_a: 2,
                n_limbs_b: 2,
                n_limbs_m: 2,
                full_m: true,
            },
            inputs: Some(MultModInputs {
                a: Integer::from(110usize),
                b: Integer::from(180usize),
                m: Integer::from(187usize),
                q: Integer::from(105usize),
                r: Integer::from(165usize),
            }),
        }, true),
        mult_mod_2w_by_6w: ( MultMod {
            params: MultModParameters {
                limb_width: 4,
                n_limbs_a: 6,
                n_limbs_b: 2,
                n_limbs_m: 2,
                full_m: true,
            },
            inputs: Some(MultModInputs {
                a: Integer::from(16777215usize),
                b: Integer::from(180usize),
                m: Integer::from(255usize),
                q: Integer::from(11842740usize),
                r: Integer::from(0usize),
            }),
        }, true),
        mult_mod_2w_by_6w_test_2: ( MultMod {
            params: MultModParameters {
                limb_width: 4,
                n_limbs_a: 6,
                n_limbs_b: 2,
                n_limbs_m: 2,
                full_m: true,
            },
            inputs: Some(MultModInputs {
                a: Integer::from(16777210usize),
                b: Integer::from(180usize),
                m: Integer::from(255usize),
                q: Integer::from(11842736usize),
                r: Integer::from(120usize),
            }),
        }, true),
        mult_mod_2048x128: ( MultMod {
            params: MultModParameters {
                limb_width: 32,
                n_limbs_a: 64,
                n_limbs_b: 4,
                n_limbs_m: 4,
                full_m: false,
            },
            inputs: Some(MultModInputs {
                a: Integer::from(16777210usize),
                b: Integer::from(180usize),
                m: Integer::from(255usize),
                q: Integer::from(11842736usize),
                r: Integer::from(120usize),
            }),
        }, true),
    }

    #[derive(Debug)]
    pub struct NumberBitDecompInputs {
        pub n: Integer,
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
            n.fits_in_bits(cs.namespace(|| "fits"), self.params.n_bits)?;
            n.decompose(cs.namespace(|| "explicit decomp"), self.params.n_bits)?;
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
                                      n: Integer::from(1usize),
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
                                      n: Integer::from(1usize),
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
                                      n: Integer::from(5usize),
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
                                      n: Integer::from(255usize),
                                  }),
                              },
                              true
                          ),
    }

    #[derive(Debug)]
    pub struct BigNatBitDecompInputs {
        pub n: Integer,
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
                n: Integer::from(n),
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
                || Ok(Integer::from_str(self.inputs.grab()?.b).unwrap()),
                self.params.limb_width,
                self.params.n_limbs_b,
            )?;
            let e = BigNat::alloc_from_nat(
                cs.namespace(|| "e"),
                || Ok(Integer::from_str(self.inputs.grab()?.e).unwrap()),
                self.params.limb_width,
                self.params.n_limbs_e,
            )?;
            let res = BigNat::alloc_from_nat(
                cs.namespace(|| "res"),
                || Ok(Integer::from_str(self.inputs.grab()?.res).unwrap()),
                self.params.limb_width,
                self.params.n_limbs_b,
            )?;
            let m = BigNat::alloc_from_nat(
                cs.namespace(|| "m"),
                || Ok(Integer::from_str(self.inputs.grab()?.m).unwrap()),
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

    #[derive(Debug)]
    pub struct MillerRabinRoundInputs<'a> {
        pub b: &'a str,
        pub n: &'a str,
        pub result: bool,
    }

    pub struct MillerRabinRoundParams {
        pub limb_width: usize,
        pub n_limbs: usize,
    }

    pub struct MillerRabinRound<'a> {
        inputs: Option<MillerRabinRoundInputs<'a>>,
        params: MillerRabinRoundParams,
    }

    impl<'a, E: Engine> Circuit<E> for MillerRabinRound<'a> {
        fn synthesize<CS: ConstraintSystem<E>>(self, cs: &mut CS) -> Result<(), SynthesisError> {
            use sapling_crypto::circuit::boolean::AllocatedBit;
            let b = BigNat::alloc_from_nat(
                cs.namespace(|| "b"),
                || Ok(Integer::from_str(self.inputs.grab()?.b).unwrap()),
                self.params.limb_width,
                self.params.n_limbs,
            )?;
            let n = BigNat::alloc_from_nat(
                cs.namespace(|| "n"),
                || Ok(Integer::from_str(self.inputs.grab()?.n).unwrap()),
                self.params.limb_width,
                self.params.n_limbs,
            )?;
            let expected_res = Boolean::Is(AllocatedBit::alloc(
                cs.namespace(|| "bit"),
                self.inputs.map(|o| o.result),
            )?);
            let actual_res = n.miller_rabin_round(cs.namespace(|| "mr"), &b)?;
            Boolean::enforce_equal(cs.namespace(|| "eq"), &expected_res, &actual_res)?;
            Ok(())
        }
    }

    circuit_tests! {
        mr_round_7_base_5: (
                               MillerRabinRound {
                                   params: MillerRabinRoundParams {
                                       limb_width: 4,
                                       n_limbs: 2,
                                   },
                                   inputs: Some(MillerRabinRoundInputs {
                                       b: "5",
                                       n: "7",
                                       result: true,
                                   }),
                               },
                               true),
                               mr_round_11_base_2: (
                                   MillerRabinRound {
                                       params: MillerRabinRoundParams {
                                           limb_width: 4,
                                           n_limbs: 2,
                                       },
                                       inputs: Some(MillerRabinRoundInputs {
                                           b: "2",
                                           n: "11",
                                           result: true,
                                       }),
                                   },
                                   true),
                                   mr_round_5_base_2: (
                                       MillerRabinRound {
                                           params: MillerRabinRoundParams {
                                               limb_width: 4,
                                               n_limbs: 2,
                                           },
                                           inputs: Some(MillerRabinRoundInputs {
                                               b: "2",
                                               n: "5",
                                               result: true,
                                           }),
                                       },
                                       false),
                                       // ~80,000 constraints
                                       mr_round_full_base_2: (
                                           MillerRabinRound {
                                               params: MillerRabinRoundParams {
                                                   limb_width: 32,
                                                   n_limbs: 4,
                                               },
                                               inputs: Some(MillerRabinRoundInputs {
                                                   b: "2",
                                                   n: "262215269494931243253999821294977607927",
                                                   result: true,
                                               }),
                                           },
                                           true),
                                           mr_round_full_base_3: (
                                               MillerRabinRound {
                                                   params: MillerRabinRoundParams {
                                                       limb_width: 32,
                                                       n_limbs: 4,
                                                   },
                                                   inputs: Some(MillerRabinRoundInputs {
                                                       b: "3",
                                                       n: "262215269494931243253999821294977607927",
                                                       result: true,
                                                   }),
                                               },
                                               true),
                                               mr_round_full_base_5: (
                                                   MillerRabinRound {
                                                       params: MillerRabinRoundParams {
                                                           limb_width: 32,
                                                           n_limbs: 4,
                                                       },
                                                       inputs: Some(MillerRabinRoundInputs {
                                                           b: "5",
                                                           n: "262215269494931243253999821294977607927",
                                                           result: true,
                                                       }),
                                                   },
                                                   true),
                                                   mr_round_full_base_2_fail: (
                                                       MillerRabinRound {
                                                           params: MillerRabinRoundParams {
                                                               limb_width: 32,
                                                               n_limbs: 4,
                                                           },
                                                           inputs: Some(MillerRabinRoundInputs {
                                                               b: "2",
                                                               n: "304740101182592084246827883024894699479",
                                                               result: false,
                                                           }),
                                                       },
                                                       true),
                                                       mr_round_full_base_3_fail: (
                                                           MillerRabinRound {
                                                               params: MillerRabinRoundParams {
                                                                   limb_width: 32,
                                                                   n_limbs: 4,
                                                               },
                                                               inputs: Some(MillerRabinRoundInputs {
                                                                   b: "3",
                                                                   n: "304740101182592084246827883024894699479",
                                                                   result: false,
                                                               }),
                                                           },
                                                           true),
                                                           mr_round_full_base_5_fail: (
                                                               MillerRabinRound {
                                                                   params: MillerRabinRoundParams {
                                                                       limb_width: 32,
                                                                       n_limbs: 4,
                                                                   },
                                                                   inputs: Some(MillerRabinRoundInputs {
                                                                       b: "5",
                                                                       n: "304740101182592084246827883024894699479",
                                                                       result: false,
                                                                   }),
                                                               },
                                                               true),
    }

    #[derive(Debug)]
    pub struct MillerRabinInputs<'a> {
        pub n: &'a str,
        pub result: bool,
    }

    pub struct MillerRabinParams {
        pub limb_width: usize,
        pub n_limbs: usize,
        pub n_rounds: usize,
    }

    pub struct MillerRabin<'a> {
        inputs: Option<MillerRabinInputs<'a>>,
        params: MillerRabinParams,
    }

    impl<'a, E: Engine> Circuit<E> for MillerRabin<'a> {
        fn synthesize<CS: ConstraintSystem<E>>(self, cs: &mut CS) -> Result<(), SynthesisError> {
            use sapling_crypto::circuit::boolean::AllocatedBit;
            let n = BigNat::alloc_from_nat(
                cs.namespace(|| "n"),
                || Ok(Integer::from_str(self.inputs.grab()?.n).unwrap()),
                self.params.limb_width,
                self.params.n_limbs,
            )?;
            let expected_res = Boolean::Is(AllocatedBit::alloc(
                cs.namespace(|| "bit"),
                self.inputs.map(|o| o.result),
            )?);
            let actual_res = n.miller_rabin(cs.namespace(|| "mr"), self.params.n_rounds)?;
            Boolean::enforce_equal(cs.namespace(|| "eq"), &expected_res, &actual_res)?;
            Ok(())
        }
    }

    circuit_tests! {
        mr_small_251: (
                          MillerRabin {
                              params: MillerRabinParams {
                                  limb_width: 4,
                                  n_limbs: 2,
                                  n_rounds: 8,
                              },
                              inputs: Some(MillerRabinInputs {
                                  n: "251",
                                  result: true,
                              }),
                          },
                          true),
                          // ~640,000 constraints
                          //mr_full: (
                          //    MillerRabin {
                          //        params: MillerRabinParams {
                          //            limb_width: 32,
                          //            n_limbs: 4,
                          //            n_rounds: 8,
                          //        },
                          //        inputs: Some(MillerRabinInputs {
                          //            n: "262215269494931243253999821294977607927",
                          //            result: true,
                          //        }),
                          //    },
                          //    true),
    }

    #[derive(Debug)]
    pub struct GcdInputs<'a> {
        pub a: &'a str,
        pub b: &'a str,
        pub gcd: &'a str,
    }

    pub struct GcdParams {
        pub limb_width: usize,
        pub n_limbs_a: usize,
        pub n_limbs_b: usize,
    }

    pub struct Gcd<'a> {
        inputs: Option<GcdInputs<'a>>,
        params: GcdParams,
    }

    impl<'a, E: Engine> Circuit<E> for Gcd<'a> {
        fn synthesize<CS: ConstraintSystem<E>>(self, cs: &mut CS) -> Result<(), SynthesisError> {
            let a = BigNat::alloc_from_nat(
                cs.namespace(|| "a"),
                || Ok(Integer::from_str(self.inputs.grab()?.a).unwrap()),
                self.params.limb_width,
                self.params.n_limbs_a,
            )?;
            let b = BigNat::alloc_from_nat(
                cs.namespace(|| "b"),
                || Ok(Integer::from_str(self.inputs.grab()?.b).unwrap()),
                self.params.limb_width,
                self.params.n_limbs_b,
            )?;
            let gcd = BigNat::alloc_from_nat(
                cs.namespace(|| "res"),
                || Ok(Integer::from_str(self.inputs.grab()?.gcd).unwrap()),
                self.params.limb_width,
                min(self.params.n_limbs_b, self.params.n_limbs_a),
            )?;
            let act = a.gcd(cs.namespace(|| "gcd"), &b)?;
            Gadget::assert_equal(cs.namespace(|| "eq"), &gcd, &act)?;
            Ok(())
        }
    }
    circuit_tests! {
        gcd_4_5: (
                     Gcd {
                         params: GcdParams {
                             limb_width: 4,
                             n_limbs_a: 1,
                             n_limbs_b: 1,
                         },
                         inputs: Some(GcdInputs {
                             a: "4",
                             b: "5",
                             gcd: "1",
                         }),
                     },
                     true),
                     gcd_4_5_unequal: (
                         Gcd {
                             params: GcdParams {
                                 limb_width: 4,
                                 n_limbs_a: 14,
                                 n_limbs_b: 5,
                             },
                             inputs: Some(GcdInputs {
                                 a: "4",
                                 b: "5",
                                 gcd: "1",
                             }),
                         },
                         true),
                         gcd_30_24: (
                             Gcd {
                                 params: GcdParams {
                                     limb_width: 4,
                                     n_limbs_a: 2,
                                     n_limbs_b: 2,
                                 },
                                 inputs: Some(GcdInputs {
                                     a: "30",
                                     b: "24",
                                     gcd: "6",
                                 }),
                             },
                             true),
                             gcd_128b: (
                                 Gcd {
                                     params: GcdParams {
                                         limb_width: 32,
                                         n_limbs_a: 4,
                                         n_limbs_b: 4,
                                     },
                                     inputs: Some(GcdInputs {
                                         a: "311515013647097972396078794914139832177",
                                         b: "298937084241820869743410128427022097023",
                                         gcd: "1",
                                     }),
                                 },
                                 true),
    }

    #[derive(Debug)]
    pub struct MillerRabin32Inputs<'a> {
        pub n: &'a str,
        pub result: bool,
    }

    pub struct MillerRabin32<'a> {
        inputs: Option<MillerRabin32Inputs<'a>>,
    }

    impl<'a, E: Engine> Circuit<E> for MillerRabin32<'a> {
        fn synthesize<CS: ConstraintSystem<E>>(self, cs: &mut CS) -> Result<(), SynthesisError> {
            use sapling_crypto::circuit::boolean::AllocatedBit;
            let n = BigNat::alloc_from_nat(
                cs.namespace(|| "n"),
                || Ok(Integer::from_str(self.inputs.grab()?.n).unwrap()),
                32,
                1,
            )?;
            let expected_res = Boolean::Is(AllocatedBit::alloc(
                cs.namespace(|| "bit"),
                self.inputs.map(|o| o.result),
            )?);
            let actual_res = n.miller_rabin_32b(cs.namespace(|| "mr"))?;
            Boolean::enforce_equal(cs.namespace(|| "eq"), &expected_res, &actual_res)?;
            Ok(())
        }
    }
    circuit_tests! {
        mr_32: (
                          MillerRabin32 {
                              inputs: Some(MillerRabin32Inputs {
                                  n: "251",
                                  result: true,
                              }),
                          },
                          true),
    }
}

impl<E: Engine> Display for BigNat<E> {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        match self.value.as_ref() {
            Some(n) => write!(f, "BigNat({})", n),
            None => write!(f, "BigNat(empty)"),
        }
    }
}

impl Debug for BigNatParams {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        f.debug_struct("BigNatParams")
            .field("limb_width", &self.limb_width)
            .field("n_limbs", &self.n_limbs)
            .field("min_bits", &self.min_bits)
            .field("max_word", &format_args!("{}", &self.max_word))
            .finish()
    }
}

impl<E: Engine> Debug for BigNat<E> {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        f.debug_struct("BigNat")
            .field("params", &self.params)
            .field("limb_values", &self.limb_values)
            .field("value", &format_args!("{}", &self))
            .finish()
    }
}
