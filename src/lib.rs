#![feature(hash_raw_entry)]

extern crate fnv;
extern crate num_bigint;
extern crate num_integer;
extern crate num_traits;
extern crate rand;
extern crate sapling_crypto;
#[macro_use]
extern crate derivative;

#[cfg(test)]
extern crate quickcheck;
#[cfg(test)]
#[macro_use(quickcheck)]
extern crate quickcheck_macros;

type CResult<T> = Result<T, SynthesisError>;

#[cfg(test)]
#[macro_use]
mod test_helpers {
    pub use sapling_crypto::bellman::pairing::bn256::Bn256;
    pub use sapling_crypto::bellman::pairing::ff::PrimeField;
    pub use sapling_crypto::bellman::Circuit;
    pub use sapling_crypto::circuit::test::TestConstraintSystem;
    macro_rules! circuit_tests {
        ($($name:ident: $value:expr,)*) => {
            $(
                #[test]
                fn $name() {
                    let (circuit, is_sat) = $value;
                    let mut cs = TestConstraintSystem::<Bn256>::new();

                    circuit.synthesize(&mut cs).expect("synthesis failed");
                    println!(concat!("Constraints in {}: {}"), stringify!($name), cs.num_constraints());
                    if is_sat && !cs.is_satisfied() {
                        println!("UNSAT: {:#?}", cs.which_is_unsatisfied())
                    }
                    let unconstrained = cs.find_unconstrained();
                    if unconstrained.len() > 0 {
                        println!(concat!("Unconstrained in {}: {}"), stringify!($name), cs.find_unconstrained());
                    }

                    assert_eq!(cs.is_satisfied(), is_sat);
                }
            )*
        }
    }
}

pub mod bench;
pub mod bignat;
pub mod bit;
pub mod entropy;
pub mod exp;
pub mod gadget;
pub mod group;
pub mod hash;
pub mod lazy;
pub mod num;
pub mod poly;
pub mod rollup;
pub mod set;
pub mod wesolowski;

use num_bigint::BigUint;
use sapling_crypto::bellman::pairing::ff::{PrimeField, PrimeFieldRepr};
use sapling_crypto::bellman::SynthesisError;

use std::str::FromStr;

trait OptionExt<T> {
    fn grab(&self) -> Result<&T, SynthesisError>;
    fn grab_mut(&mut self) -> Result<&mut T, SynthesisError>;
}

impl<T> OptionExt<T> for Option<T> {
    fn grab(&self) -> Result<&T, SynthesisError> {
        self.as_ref().ok_or(SynthesisError::AssignmentMissing)
    }
    fn grab_mut(&mut self) -> Result<&mut T, SynthesisError> {
        self.as_mut().ok_or(SynthesisError::AssignmentMissing)
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
pub fn usize_to_f<F: PrimeField>(n: usize) -> F {
    F::from_str(&format!("{}", n)).unwrap()
}

/// Convert a `usize` to a field element.
/// Panics if the field is too small.
pub fn f_to_usize<F: PrimeField>(n: F) -> usize {
    let s = format!("{}", n);
    usize::from_str_radix(&(s.as_str()[6..(s.len()-1)]), 16).unwrap()
}
