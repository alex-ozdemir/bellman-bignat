#![allow(non_snake_case)]

use bitintr::Mulx;
use gmp_mpfr_sys::gmp::limb_t;
use rug::Integer;
use serde::{Deserialize, Serialize};

use std::mem::size_of;
use std::ptr::{copy, write_bytes};

use super::parallel_product::borrow_digits;

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
    /// The negated inverse of n, modulo R
    N_inv_neg: Integer,
    /// The produce of R and N
    RN: Integer,
    /// The negated inverse of N modulo B
    N_inv_neg_B: limb_t,
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
        let B = Integer::from(1) << b;
        let N_inv_neg_B = (-N.clone()).invert(&B).unwrap();
        assert!(N_inv_neg_B.significant_bits() <= b);
        Self {
            N,
            RmodN,
            R2modN,
            log2_R,
            r,
            N_inv_neg,
            RN,
            N_inv_neg_B: borrow_digits(&N_inv_neg_B)[0].clone(),
        }
    }

    /// This implementation of Montgomery reduction uses GMP instead of implementing the
    /// multiprecision algorithm. The thought is that GMP will do a better job. We'll see.
    pub fn redc(&self, mut T: Integer) -> Integer {
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

    /// This is an implementation of multiprecision Montgomery reduction.
    #[allow(dead_code)]
    pub fn redc_mp(&self, mut Ti: Integer) -> Integer {
        let Np = self.N_inv_neg_B;
        let N = borrow_digits(&self.N);
        let r = self.r as usize;
        let p = N.len();

        // We need to grow the integer to be at least as big as N, and then an extra space for any
        // carry.
        let min_T_size = r + p + 1;
        Ti.reserve(size_of::<limb_t>() * 8 * min_T_size - Ti.significant_bits() as usize);
        debug_assert!(Ti.capacity() >= size_of::<limb_t>() * 8 * min_T_size);

        unsafe {
            let T: *mut limb_t = (*Ti.as_raw_mut()).d;
            write_bytes(T.add(Ti.significant_digits::<limb_t>()), 0, min_T_size - Ti.significant_digits::<limb_t>());
            for i in 0..r {
                let mut c = 0;
                let m = limb_t::mulx(*T.add(i), Np).0;
                for j in 0..p {
                    let x =
                        *T.add(i + j) as u128 + m as u128 * *N.get_unchecked(j) as u128 + c as u128;
                    *T.add(i + j) = x as limb_t;
                    c = (x >> (8 * size_of::<limb_t>())) as limb_t;
                }
                for j in p..(min_T_size - i) {
                    let x = *T.add(i + j) as u128 + c as u128;
                    *T.add(i + j) = x as limb_t;
                    c = (x >> (8 * size_of::<limb_t>())) as limb_t;
                }
                debug_assert_eq!(*T.add(i), 0);
            }
            let size = (1..=p)
                .rev()
                .find(|s| *T.add(r + s - 1) != 0)
                .unwrap_or(0);
            copy(T.add(r), T, size);
            (*Ti.as_raw_mut()).size = size as i32;
        }
        if Ti > self.N {
            Ti - &self.N
        } else {
            Ti
        }
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
pub struct MontyNum(pub Integer);

#[cfg(test)]
mod tests {
    use super::*;
    use test::*;
    use rug::rand::RandState;
    use std::str::FromStr;
    const RSA_2048: &str = "25195908475657893494027183240048398571429282126204032027777137836043662020707595556264018525880784406918290641249515082189298559149176184502808489120072844992687392807287776735971418347270261896375014971824691165077613379859095700097330459748808428401797429100642458691817195118746121515172654632282216869987549182422433637259085141865462043576798423387184774447920739934236584823824281198163815010674810451660377306056201619676256133844143603833904414952634432190114657544454178424020924616515723350778707749817125772467962926386356373289912154831438167899885040445364023527381951378636564391212010397122822120720357";

    /// Random operations on an integer, more or less.
    fn operate(i: &mut Integer) {
        let n = Integer::from_str(
            "45032408257293263260773906994099777552173939956523527117391050121724017348167",
        )
        .unwrap();
        *i += &n;
        *i *= &n;
        *i %= &n;
        *i <<= 16;
        *i /= &n;
    }

    #[test]
    fn redc_equivalence_tiny() {
        let n = Integer::from_str("14003342538859904917").unwrap();
        let monty = MontyConstants::new(n.clone());
        let input = Integer::from(1);

        // Use both versions of REDC, assert result equivalence
        let mut expect = monty.redc(input.clone());
        let mut result = monty.redc_mp(input);
        assert_eq!(expect, result);

        // Do subsequent operations, assert result equivalence
        // Important because redc_mp fiddles with internals.
        // A bug could want to mess them up.
        operate(&mut expect);
        operate(&mut result);
        assert_eq!(expect, result);
    }

    #[test]
    fn redc_equivalence_small() {
        let n = Integer::from_str("318475643993954790644818855069112088563").unwrap();
        let monty = MontyConstants::new(n.clone());
        let input = Integer::from(1);

        // Use both versions of REDC, assert result equivalence
        let mut expect = monty.redc(input.clone());
        let mut result = monty.redc_mp(input);
        assert_eq!(expect, result);

        // Do subsequent operations, assert result equivalence
        // Important because redc_mp fiddles with internals.
        // A bug could want to mess them up.
        operate(&mut expect);
        operate(&mut result);
        assert_eq!(expect, result);
    }

    #[test]
    fn redc_equivalence_medium() {
        let n = Integer::from_str(
            "109910236399443861266704537898162531048702512880173728452112705364178785050797",
        )
        .unwrap();
        let monty = MontyConstants::new(n.clone());
        let input = Integer::from_str(
            "45032408257293263260773906994099777552173939956523527117391050121724017348167",
        )
        .unwrap();

        // Use both versions of REDC, assert result equivalence
        let mut expect = monty.redc(input.clone());
        let mut result = monty.redc_mp(input);
        assert_eq!(expect, result);

        // Do subsequent operations, assert result equivalence
        // Important because redc_mp fiddles with internals.
        // A bug could want to mess them up.
        operate(&mut expect);
        operate(&mut result);
        assert_eq!(expect, result);
    }

    #[test]
    fn redc_equivalence_large() {
        let mut rnd = RandState::new();
        const BITS: u32 = 2047;
        _seed_rng(&mut rnd);
        let monty = MontyConstants::new(Integer::from_str(RSA_2048).unwrap());

        let input = Integer::from(Integer::random_bits(BITS, &mut rnd));

        // Use both versions of REDC, assert result equivalence
        let mut expect = monty.redc(input.clone());
        let mut result = monty.redc_mp(input);
        assert_eq!(expect, result);

        // Do subsequent operations, assert result equivalence
        // Important because redc_mp fiddles with internals.
        // A bug could want to mess them up.
        operate(&mut expect);
        operate(&mut result);
        assert_eq!(expect, result);
    }

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

    #[bench]
    fn bench_redc(b: &mut Bencher) {
        let mut rnd = RandState::new();
        const BITS: u32 = 2048;
        _seed_rng(&mut rnd);
        let n = Integer::from_str(RSA_2048).unwrap();
        let monty = MontyConstants::new(n.clone());
        let mut input = Integer::from(Integer::random_bits(BITS, &mut rnd));
        input.reserve(10000);
        let expected = monty.redc_mp(input.clone());
        b.iter(|| assert_eq!(expected, monty.redc(input.clone())));
    }

    #[bench]
    fn bench_redc_mp(b: &mut Bencher) {
        let mut rnd = RandState::new();
        const BITS: u32 = 2048;
        _seed_rng(&mut rnd);
        let n = Integer::from_str(RSA_2048).unwrap();
        let monty = MontyConstants::new(n.clone());
        let mut input = Integer::from(Integer::random_bits(BITS, &mut rnd));
        input.reserve(10000);
        let expected = monty.redc(input.clone());
        b.iter(|| assert_eq!(expected, monty.redc_mp(input.clone())));
    }

    #[bench]
    fn bench_gmp_mult(b: &mut Bencher) {
        let mut rnd = RandState::new();
        const BITS: u32 = 2048;
        _seed_rng(&mut rnd);
        let n = Integer::from_str(RSA_2048).unwrap();
        let input1 = Integer::from(Integer::random_bits(BITS, &mut rnd));
        let input2 = Integer::from(Integer::random_bits(BITS, &mut rnd));
        let expected = input1.clone() * &input2 % &n;
        b.iter(|| assert_eq!(expected, input1.clone() * &input2 % &n));
    }

    #[bench]
    fn bench_monty_redc_mult(b: &mut Bencher) {
        let mut rnd = RandState::new();
        const BITS: u32 = 2048;
        _seed_rng(&mut rnd);
        let n = Integer::from_str(RSA_2048).unwrap();
        let monty = MontyConstants::new(n.clone());
        let input1 = monty.in_to(Integer::from(Integer::random_bits(BITS, &mut rnd)));
        let input2 = monty.in_to(Integer::from(Integer::random_bits(BITS, &mut rnd)));
        let expected = monty.mult(input1.clone(), &input2);
        b.iter(|| assert_eq!(expected, monty.mult(input1.clone(), &input2)));
    }

    #[bench]
    fn bench_monty_redc_mp_mult(b: &mut Bencher) {
        let mut rnd = RandState::new();
        const BITS: u32 = 2048;
        _seed_rng(&mut rnd);
        let n = Integer::from_str(RSA_2048).unwrap();
        let monty = MontyConstants::new(n.clone());
        let input1 = monty.in_to(Integer::from(Integer::random_bits(BITS, &mut rnd)));
        let input2 = monty.in_to(Integer::from(Integer::random_bits(BITS, &mut rnd)));
        b.iter(|| monty.redc(input1.0.clone() * &input2.0));
    }
}
