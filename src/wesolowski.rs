use num_bigint::BigUint;
use num_traits::One;
use sapling_crypto::bellman::{ConstraintSystem, SynthesisError};
use sapling_crypto::bellman::pairing::Engine;

use bignat::BigNat;
use OptionExt;

/// Computes `b ^ (prod(xs) / l) % m`, cleverly.
pub fn base_to_product<'a, I: Iterator<Item = &'a BigUint>>(
    b: &BigUint,
    l: &BigUint,
    m: &BigUint,
    xs: I,
) -> BigUint {
    base_to_product_helper(&BigUint::one(), b, l, m, xs).0
}

/// Computes `b ^ (a * prod(xs) / l) % m` and `b ^ prod(x) % m`.
pub fn base_to_product_helper<'a, I: Iterator<Item = &'a BigUint>>(
    a: &BigUint,
    b: &BigUint,
    l: &BigUint,
    m: &BigUint,
    mut xs: I,
) -> (BigUint, BigUint) {
    if let Some(x) = xs.next() {
        let (rq, rp) = base_to_product_helper(&(a * x % l), b, l, m, xs);
        (rp.modpow(&(a * x / l), &m) * rq % m, rp.modpow(&x, &m))
    } else {
        (b.modpow(&(a / l), m), b.clone())
    }
}

/// Computes `b ^ (prod(xs) / l) % m`, naively.
pub fn base_to_product_naive<'a, I: Iterator<Item = &'a BigUint>>(
    b: &BigUint,
    l: &BigUint,
    m: &BigUint,
    xs: I,
) -> BigUint {
    let mut pow = BigUint::one();
    for x in xs {
        pow *= x;
    }
    pow /= l;
    b.modpow(&pow, m)
}

/// \exists q s.t. q^l \times base^r = result
pub fn proof_of_exp<E: Engine, CS: ConstraintSystem<E>>(
    mut cs: CS,
    base: &BigNat<E>,
    modulus: &BigNat<E>,
    power_factors: &[BigNat<E>],
    challenge: &BigNat<E>,
    result: &BigNat<E>,
) -> Result<(), SynthesisError> {
    if base.limb_width != modulus.limb_width
        || base.limb_width != result.limb_width
        || base.limbs.len() != modulus.limbs.len()
        || base.limbs.len() != result.limbs.len()
    {
        return Err(SynthesisError::Unsatisfiable);
    }
    let q_computation = || -> Result<BigUint, SynthesisError> {
        Ok(base_to_product(
            base.value.grab()?,
            challenge.value.grab()?,
            modulus.value.grab()?,
            power_factors
                .iter()
                .map(|pow| pow.value.grab())
                .collect::<Result<Vec<_>, _>>()?
                .into_iter(),
        ))
    };
    let r_computation = || -> Result<BigUint, SynthesisError> {
        let mut prod = BigUint::one();
        let l = challenge.value.grab()?;
        for pow in power_factors {
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
    println!("Q allocated");
    let r = BigNat::alloc_from_nat(
        cs.namespace(|| "r"),
        r_computation,
        challenge.limb_width,
        challenge.limbs.len(),
    )?;
    println!("r allocated");
    let ql = q.pow_mod(cs.namespace(|| "Q^l"), &challenge, &modulus)?;
    println!("Q^l synthesized");
    let br = base.pow_mod(cs.namespace(|| "b^r"), &r, &modulus)?;
    println!("b^r synthesized");
    let left = ql.mult_mod(cs.namespace(|| "Q^l b^r"), &br, &modulus)?.1;
    println!("left synthesized");
    left.equal(cs.namespace(|| "Q^l b^r == res"), &result)
}



#[cfg(test)]
mod tests {
    use super::*;

    use test_helpers::*;
    use quickcheck::TestResult;


    use std::str::FromStr;

    pub struct PoEInputs<'a> {
        pub b: &'a str,
        pub exps: &'a [&'a str],
        pub l: &'a str,
        pub m: &'a str,
        pub res: Option<&'a str>, // If missing, it will be computed
    }

    pub struct PoEParams {
        pub limb_width: usize,
        pub n_limbs_b: usize,
        pub n_limbs_e: usize,
    }

    pub struct PoE<'a> {
        inputs: Option<PoEInputs<'a>>,
        params: PoEParams,
    }

    circuit_tests! {
        proof_1_to_1: (
                          PoE {
                              params: PoEParams {
                                  limb_width: 4,
                                  n_limbs_b: 2,
                                  n_limbs_e: 1,
                              },
                              inputs: Some(PoEInputs {
                                  b: "1",
                                  m: "255",
                                  exps: &["1"],
                                  l: "15",
                                  res: Some("1"),
                              }),
                          },
                          true
                      ),
                      proof_1_to_1_2_3_4_15: (
                          PoE {
                              params: PoEParams {
                                  limb_width: 4,
                                  n_limbs_b: 2,
                                  n_limbs_e: 1,
                              },
                              inputs: Some(PoEInputs {
                                  b: "1",
                                  m: "255",
                                  exps: &[
                                      "1",
                                      "2",
                                      "3",
                                      "4",
                                      "15",
                                  ],
                                  l: "15",
                                  res: Some("1"),
                              }),
                          },
                          true
                              ),
                              proof_2_to_1_2_3_4_15_wrong: (
                                  PoE {
                                      params: PoEParams {
                                          limb_width: 4,
                                          n_limbs_b: 2,
                                          n_limbs_e: 1,
                                      },
                                      inputs: Some(PoEInputs {
                                          b: "2",
                                          m: "255",
                                          exps: &[
                                              "1",
                                              "2",
                                              "3",
                                              "4",
                                              "15",
                                          ],
                                          l: "15",
                                          res: Some("16"),
                                      }),
                                  },
                                  false
                                      ),
                                      proof_2_to_1_2_3_4_15: (
                                          PoE {
                                              params: PoEParams {
                                                  limb_width: 4,
                                                  n_limbs_b: 2,
                                                  n_limbs_e: 1,
                                              },
                                              inputs: Some(PoEInputs {
                                                  b: "2",
                                                  m: "255",
                                                  exps: &[
                                                      "1",
                                                      "2",
                                                      "3",
                                                      "4",
                                                      "15",
                                                  ],
                                                  l: "15",
                                                  res: None,
                                              }),
                                          },
                                          true
                                              ),
                                              proof_7_to_many_powers: (
                                                  PoE {
                                                      params: PoEParams {
                                                          limb_width: 4,
                                                          n_limbs_b: 2,
                                                          n_limbs_e: 1,
                                                      },
                                                      inputs: Some(PoEInputs {
                                                          b: "7",
                                                          m: "255",
                                                          exps: &[
                                                              "1",
                                                              "2",
                                                              "3",
                                                              "4",
                                                              "9",
                                                              "4",
                                                              "11",
                                                              "15",
                                                              "4",
                                                              "15",
                                                          ],
                                                          l: "13",
                                                          res: None,
                                                      }),
                                                  },
                                                  true
                                                      ),
    }

    impl<'a, E: Engine> Circuit<E> for PoE<'a> {
        fn synthesize<CS: ConstraintSystem<E>>(self, cs: &mut CS) -> Result<(), SynthesisError> {
            let b = BigNat::alloc_from_nat(
                cs.namespace(|| "b"),
                || Ok(BigUint::from_str(self.inputs.grab()?.b).unwrap()),
                self.params.limb_width,
                self.params.n_limbs_b,
            )?;
            let exps = self
                .inputs
                .grab()?
                .exps
                .iter()
                .enumerate()
                .map(|(i, e)| {
                    BigNat::alloc_from_nat(
                        cs.namespace(|| format!("e {}", i)),
                        || Ok(BigUint::from_str(e).unwrap()),
                        self.params.limb_width,
                        self.params.n_limbs_e,
                    )
                })
                .collect::<Result<Vec<BigNat<E>>, SynthesisError>>()?;
            let res_computation = || -> Result<BigUint, SynthesisError> {
                let ref inputs = self.inputs.grab()?;
                inputs
                    .res
                    .map(|r| Ok(BigUint::from_str(r).unwrap()))
                    .unwrap_or_else(|| {
                        let mut acc = BigUint::from_str(inputs.b).unwrap();
                        let m = BigUint::from_str(inputs.m).unwrap();
                        for p in inputs.exps {
                            acc = acc.modpow(&BigUint::from_str(p).unwrap(), &m);
                        }
                        Ok(acc)
                    })
            };
            let res = BigNat::alloc_from_nat(
                cs.namespace(|| "res"),
                res_computation,
                self.params.limb_width,
                self.params.n_limbs_b,
            )?;
            let m = BigNat::alloc_from_nat(
                cs.namespace(|| "m"),
                || Ok(BigUint::from_str(self.inputs.grab()?.m).unwrap()),
                self.params.limb_width,
                self.params.n_limbs_b,
            )?;
            let l = BigNat::alloc_from_nat(
                cs.namespace(|| "l"),
                || Ok(BigUint::from_str(self.inputs.grab()?.l).unwrap()),
                self.params.limb_width,
                self.params.n_limbs_b,
            )?;
            proof_of_exp(cs.namespace(|| "proof of exp"), &b, &m, &exps, &l, &res)
        }
    }

    #[test]
    fn base_to_product_0() {
        let b = BigUint::from(2usize);
        let m = BigUint::from(2usize);
        let l = BigUint::from(2usize);
        let xs = [
            BigUint::from(1usize),
            BigUint::from(1usize),
            BigUint::from(1usize),
        ];
        let clever = base_to_product(&b, &l, &m, xs.iter());
        assert_eq!(clever, BigUint::from(1usize));
    }

    #[test]
    fn base_to_product_1() {
        let b = BigUint::from(2usize);
        let xs = [
            BigUint::from(4usize),
            BigUint::from(3usize),
            BigUint::from(1usize),
        ];
        let l = BigUint::from(3usize);
        let m = BigUint::from(3usize);
        let clever = base_to_product(&b, &l, &m, xs.iter());
        assert_eq!(clever, BigUint::from(1usize));
    }

    #[quickcheck]
    fn qc_naive_and_clever_base_to_product_agree(
        b: u8,
        x0: u8,
        x1: u8,
        x2: u8,
        l: u8,
        m: u8,
    ) -> TestResult {
        if b < 1 {
            return TestResult::discard();
        }
        let b = BigUint::from(b);
        if m < 2 {
            return TestResult::discard();
        }
        let m = BigUint::from(m);
        if l < 2 {
            return TestResult::discard();
        }
        let l = BigUint::from(l);
        let xs = [BigUint::from(x0), BigUint::from(x1), BigUint::from(x2)];
        let clever = base_to_product(&b, &l, &m, xs.iter());
        let naive = base_to_product_naive(&b, &l, &m, xs.iter());
        TestResult::from_bool(clever == naive)
    }

    #[quickcheck]
    fn qc_proof_of_exp(b: u8, x0: u8, x1: u8, x2: u8, l: u8) -> TestResult {
        if b < 1 {
            return TestResult::discard();
        }
        if l < 2 {
            return TestResult::discard();
        }
        let b = format!("{}", b);
        let x0 = format!("{}", x0);
        let x1 = format!("{}", x1);
        let x2 = format!("{}", x2);
        let l = format!("{}", l);
        let m = "255";
        let xs: &[&str] = &[&x0, &x1, &x2];
        let circuit = PoE {
            inputs: Some(PoEInputs {
                b: &b,
                m: &m,
                l: &l,
                exps: xs,
                res: None,
            }),
            params: PoEParams {
                limb_width: 4,
                n_limbs_b: 2,
                n_limbs_e: 2,
            },
        };
        let mut cs = TestConstraintSystem::<Bn256>::new();

        circuit.synthesize(&mut cs).expect("synthesis failed");
        if !cs.is_satisfied() {
            println!("UNSAT: {:#?}", cs.which_is_unsatisfied())
        }

        TestResult::from_bool(cs.is_satisfied())
    }
}
