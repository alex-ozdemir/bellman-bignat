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
    pub log2_R: u32,
    /// The logarithm of R, base B (the limb base).
    r: u32,
    /// The inverse of n, modulo R
    pub N_inv_neg: Integer,
    /// The produce of R and N
    RN: Integer,
}

impl MontyConstants {
    pub fn new(N: Integer) -> Self {
        let b = size_of::<limb_t>() as u32 * 8;
        let r = (N.significant_bits() - 1) / b + 1;
        let log2_R = r * b;
        let R = Integer::from(1) << log2_R;
        let RmodN = R.clone() % &N;
        let R2modN = RmodN.clone() * &RmodN % &N;
        let N_inv_neg = (-N.clone()).invert(&R).unwrap();
        let RN = R * &N;
        Self {
            N,
            RmodN,
            R2modN,
            log2_R,
            r,
            N_inv_neg,
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
        m *= &self.N_inv_neg;
        m.keep_bits_mut(self.log2_R);
        m *= &self.N;
        T += &m;
        debug_assert_eq!(T.clone().keep_bits(self.log2_R), Integer::from(0));
        T >>= self.log2_R;
        if &T >= &self.N {
            T -= &self.N;
        }
        T
    }

    pub fn in_to(&self, i: Integer) -> MontyNum {
        MontyNum(self.redc(i * &self.R2modN))
    }

    pub fn out_of(&self, n: MontyNum) -> Integer {
        self.redc(n.0)
    }

    pub fn mult(&self, i: MontyNum, j: &MontyNum) -> MontyNum {
        MontyNum(self.redc(i.0 * &j.0))
    }

    pub fn square(&self, i: MontyNum) -> MontyNum {
        MontyNum(self.redc(i.0.square()))
    }
}

#[derive(Clone, Debug, Deserialize, Serialize, PartialEq, Eq)]
pub struct MontyNum(Integer);

#[cfg(test)]
mod tests {
    use super::*;
    use rug::rand::RandState;
    use std::str::FromStr;
    const RSA_2048: &str = "25195908475657893494027183240048398571429282126204032027777137836043662020707595556264018525880784406918290641249515082189298559149176184502808489120072844992687392807287776735971418347270261896375014971824691165077613379859095700097330459748808428401797429100642458691817195118746121515172654632282216869987549182422433637259085141865462043576798423387184774447920739934236584823824281198163815010674810451660377306056201619676256133844143603833904414952634432190114657544454178424020924616515723350778707749817125772467962926386356373289912154831438167899885040445364023527381951378636564391212010397122822120720357";

    #[test]
    fn in_out() {
        let mut rnd = RandState::new();
        const BITS: u32 = 2047;
        _seed_rng(&mut rnd);
        let monty = MontyConstants::new(Integer::from_str(RSA_2048).unwrap());

        let expect = Integer::from(Integer::random_bits(BITS, &mut rnd));
        let m = monty.in_to(expect.clone());
        let result = monty.out_of(m);

        assert_eq!(expect, result);
    }

    #[test]
    fn product() {
        let mut rnd = RandState::new();
        const BITS: u32 = 2047;
        _seed_rng(&mut rnd);
        let n = Integer::from_str(RSA_2048).unwrap();
        let monty = MontyConstants::new(n.clone());

        let a = Integer::from(Integer::random_bits(BITS, &mut rnd));
        let b = Integer::from(Integer::random_bits(BITS, &mut rnd));
        let expect = a.clone() * &b % &n;
        let result = monty.out_of(monty.mult(monty.in_to(a), &monty.in_to(b)));
        assert_eq!(expect, result);
    }

    #[test]
    fn square() {
        let mut rnd = RandState::new();
        const BITS: u32 = 2047;
        _seed_rng(&mut rnd);
        let n = Integer::from_str(RSA_2048).unwrap();
        let monty = MontyConstants::new(n.clone());

        let a = Integer::from(Integer::random_bits(BITS, &mut rnd));
        let expect = a.clone() * &a % &n;
        let result = monty.out_of(monty.square(monty.in_to(a)));
        assert_eq!(expect, result);
    }

    fn _seed_rng(rnd: &mut RandState) {
        use rug::integer::Order;
        rnd.seed(&Integer::from_digits(
            &rand::random::<[u64; 4]>()[..],
            Order::Lsf,
        ));
    }

}
