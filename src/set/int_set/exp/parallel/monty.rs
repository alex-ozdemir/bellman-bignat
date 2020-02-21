#![allow(non_snake_case)]

use gmp_mpfr_sys::gmp::limb_t;
use serde::{Deserialize, Serialize};
use rug::Integer;

use std::mem::size_of;

#[derive(Clone, Debug, Deserialize, Serialize, PartialEq, Eq)]
pub struct MontyConstants {
    /// The modulus
    N: Integer,
    /// The base of arithmetic, R, mod N
    RmodN: Integer,
    /// R^2, mod M
    R2modN: Integer,
    log2_R: u32,
    /// The logarithm of R, base B (the limb base).
    r: u32,
    /// The inverse of n, modulo R
    N_inv: Integer,
    /// The produce of R and N
    RN: Integer,
}

impl MontyConstants {
    pub fn new(N: Integer) -> Self {
        let b = size_of::<limb_t>() as u32;
        let r = (N.significant_bits() - 1) / b + 1;
        let log2_R = r * b;
        let R = Integer::from(1) << log2_R;
        let RmodN = R.clone() % &N;
        let R2modN = RmodN.clone() * &RmodN % &N;
        let N_inv = N.clone().invert(&R).unwrap();
        let RN = R * &N;
        Self {
            N,
            RmodN,
            R2modN,
            log2_R,
            r,
            N_inv,
            RN,
        }
    }

    /// This implementation of Montgomery reduction uses GMP instead of implementing the
    /// multiprecision algorithm. The thought is that GMP will do a better job. We'll see.
    fn redc(&self, mut T: Integer) -> Integer {
        debug_assert!(&T < &self.RN);
        debug_assert!(&0 <= &T);
        let mut m = T.clone();
        m.keep_bits_mut(self.log2_R);
        m *= &self.N_inv;
        m.keep_bits_mut(self.log2_R);
        m *= &self.N;
        T += &m;
        T >>= self.log2_R;
        if &T >= &self.N {
            T -= &self.N;
        }
        T
    }

    pub fn into(&self, i: Integer) -> MontyNum {
        MontyNum(self.redc(i * &self.R2modN))
    }

    pub fn out_of(&self, n: MontyNum) -> Integer {
        self.redc(n.0 * &self.RmodN)
    }

    pub fn product(&self, i: MontyNum, j: &MontyNum) -> MontyNum {
        MontyNum(self.redc(i.0 * &j.0))
    }
}

pub struct MontyNum(Integer);
