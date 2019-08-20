extern crate bellman;
extern crate ff;
extern crate pairing;
extern crate rand;
extern crate sapling_crypto;
extern crate num_bigint;
extern crate num_traits;

#[cfg(test)]
extern crate quickcheck;
#[cfg(test)]
#[macro_use(quickcheck)]
extern crate quickcheck_macros;

pub mod bit;
pub mod num;
pub mod poly;
pub mod bignat;
pub mod lazy;
pub mod acc;

use ff::{PrimeField, PrimeFieldRepr};
use num_bigint::BigUint;
use bellman::SynthesisError;

trait OptionExt<T> {
    fn grab(&self) -> Result<&T, SynthesisError>;
}

impl<T> OptionExt<T> for Option<T> {
    fn grab(&self) -> Result<&T, SynthesisError> {
        self.as_ref().ok_or(SynthesisError::AssignmentMissing)
    }
}

/// Convert a field element to a natural number
fn f_to_nat<F: PrimeField>(f: &F) -> BigUint {
    let mut s = Vec::new();
    f.into_repr().write_be(&mut s).unwrap();
    BigUint::from_bytes_be(&s)
}

/// Convert a natural number to a field element.
/// Returns `None` if the number is too big for the field.
fn nat_to_f<F: PrimeField>(n: &BigUint) -> Option<F> {
    F::from_str(&format!("{}", n))
}

/// Convert a `usize` to a field element.
/// Panics if the field is too small.
fn usize_to_f<F: PrimeField>(n: usize) -> F {
    F::from_str(&format!("{}", n)).unwrap()
}

