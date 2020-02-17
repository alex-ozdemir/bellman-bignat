use rug::{integer::Order, Integer};
use sapling_crypto::bellman::pairing::ff::{PrimeField, PrimeFieldRepr};

/// Convert a field element to a natural number
pub fn f_to_nat<F: PrimeField>(f: &F) -> Integer {
    let mut s = Vec::new();
    f.into_repr().write_be(&mut s).unwrap();
    Integer::from_digits(f.into_repr().as_ref(), Order::Lsf)
}

/// Convert a natural number to a field element.
/// Returns `None` if the number is too big for the field.
pub fn nat_to_f<F: PrimeField>(n: &Integer) -> Option<F> {
    F::from_str(&format!("{}", n))
}

/// Convert a `usize` to a field element.
/// Panics if the field is too small.
pub fn usize_to_f<F: PrimeField>(n: usize) -> F {
    F::from_repr(<F::Repr as From<u64>>::from(n as u64)).expect("decoding problem")
}

/// Convert a `usize` to a field element.
/// Panics if the field is too small.
pub fn f_to_usize<F: PrimeField>(n: &F) -> usize {
    let s = n.into_repr();
    assert!(s.as_ref().iter().skip(1).all(|v| *v == 0));
    s.as_ref()[0] as usize
}

#[cfg(test)]
mod test {
    use super::*;
    use sapling_crypto::bellman::pairing::bn256::Fr;
    use sapling_crypto::bellman::pairing::ff::PrimeField;

    #[test]
    fn test_nat_to_f() {
        let n = Integer::from(4usize);
        let e = Fr::from_str("4").unwrap();
        assert!(nat_to_f::<Fr>(&n).unwrap() == e);
    }

    #[test]
    fn test_f_to_nat() {
        let n = Integer::from(4usize);
        let e = Fr::from_str("4").unwrap();
        assert!(f_to_nat(&e) == n)
    }

    #[test]
    fn test_usize_to_f() {
        let n = 4usize;
        let e = Fr::from_str("4").unwrap();
        assert!(usize_to_f::<Fr>(n) == e);
    }

    #[test]
    fn test_f_to_usize() {
        let n = 4usize;
        let e = Fr::from_str("4").unwrap();
        assert!(f_to_usize(&e) == n)
    }
}
