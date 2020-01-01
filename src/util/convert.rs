use num_bigint::BigUint;
use sapling_crypto::bellman::pairing::ff::{PrimeField, PrimeFieldRepr};

/// Convert a field element to a natural number
pub fn f_to_nat<F: PrimeField>(f: &F) -> BigUint {
    let mut s = Vec::new();
    f.into_repr().write_be(&mut s).unwrap();
    BigUint::from_bytes_be(&s)
}

/// Convert a natural number to a field element.
/// Returns `None` if the number is too big for the field.
pub fn nat_to_f<F: PrimeField>(n: &BigUint) -> Option<F> {
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
