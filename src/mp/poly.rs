use sapling_crypto::bellman::pairing::ff::Field;
use sapling_crypto::bellman::pairing::Engine;
use sapling_crypto::bellman::{ConstraintSystem, LinearCombination, SynthesisError};

use std::cmp::max;
use std::fmt::{self, Debug, Formatter};

use OptionExt;

pub struct Polynomial<E: Engine> {
    pub coefficients: Vec<LinearCombination<E>>,
    pub values: Option<Vec<E::Fr>>,
}

impl<E: Engine> Debug for Polynomial<E> {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        f.debug_struct("Polynomial")
            .field("values", &self.values)
            .finish()
    }
}

impl<E: Engine> Polynomial<E> {
    pub fn evaluate_at(&self, x: E::Fr) -> Option<E::Fr> {
        self.values.as_ref().map(|vs| {
            let mut v = E::Fr::one();
            let mut acc = E::Fr::zero();
            for coeff in vs {
                let mut t = coeff.clone();
                t.mul_assign(&v);
                acc.add_assign(&t);
                v.mul_assign(&x);
            }
            acc
        })
    }
    pub fn alloc_product<CS: ConstraintSystem<E>>(
        &self,
        mut cs: CS,
        other: &Self,
    ) -> Result<Polynomial<E>, SynthesisError> {
        let n_product_coeffs = self.coefficients.len() + other.coefficients.len() - 1;
        let values = self.values.as_ref().and_then(|self_vs| {
            other.values.as_ref().map(|other_vs| {
                let mut values: Vec<E::Fr> = std::iter::repeat_with(E::Fr::zero)
                    .take(n_product_coeffs)
                    .collect();
                for (self_i, self_v) in self_vs.iter().enumerate() {
                    for (other_i, other_v) in other_vs.iter().enumerate() {
                        let mut v = self_v.clone();
                        v.mul_assign(other_v);
                        values[self_i + other_i].add_assign(&v);
                    }
                }
                values
            })
        });
        let coefficients = (0..n_product_coeffs)
            .map(|i| {
                Ok(LinearCombination::zero()
                    + cs.alloc(|| format!("prod {}", i), || Ok(values.grab()?[i].clone()))?)
            })
            .collect::<Result<Vec<LinearCombination<E>>, SynthesisError>>()?;
        let product = Polynomial {
            coefficients,
            values,
        };
        let one = E::Fr::one();
        let mut x = E::Fr::zero();
        for _ in 1..(n_product_coeffs + 1) {
            x.add_assign(&one);
            cs.enforce(
                || format!("pointwise product @ {}", x),
                |lc| {
                    let mut i = E::Fr::one();
                    self.coefficients.iter().fold(lc, |lc, c| {
                        let r = lc + (i, c);
                        i.mul_assign(&x);
                        r
                    })
                },
                |lc| {
                    let mut i = E::Fr::one();
                    other.coefficients.iter().fold(lc, |lc, c| {
                        let r = lc + (i, c);
                        i.mul_assign(&x);
                        r
                    })
                },
                |lc| {
                    let mut i = E::Fr::one();
                    product.coefficients.iter().fold(lc, |lc, c| {
                        let r = lc + (i, c);
                        i.mul_assign(&x);
                        r
                    })
                },
            )
        }
        Ok(product)
    }

    pub fn sum(&self, other: &Self) -> Self {
        let n_coeffs = max(self.coefficients.len(), other.coefficients.len());
        let values = self.values.as_ref().and_then(|self_vs| {
            other.values.as_ref().map(|other_vs| {
                (0..n_coeffs)
                    .map(|i| {
                        let mut s = E::Fr::zero();
                        if i < self_vs.len() {
                            s.add_assign(&self_vs[i]);
                        }
                        if i < other_vs.len() {
                            s.add_assign(&other_vs[i]);
                        }
                        s
                    })
                    .collect()
            })
        });
        let coefficients = (0..n_coeffs)
            .map(|i| {
                let mut lc = LinearCombination::zero();
                if i < self.coefficients.len() {
                    lc = lc + &self.coefficients[i];
                }
                if i < other.coefficients.len() {
                    lc = lc + &other.coefficients[i];
                }
                lc
            })
            .collect();
        Polynomial {
            coefficients,
            values,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use sapling_crypto::bellman::pairing::bn256::{Bn256, Fr};
    use sapling_crypto::bellman::Circuit;
    use sapling_crypto::circuit::test::TestConstraintSystem;

    pub struct PolynomialMultiplier<E: Engine> {
        pub a: Vec<E::Fr>,
        pub b: Vec<E::Fr>,
    }

    impl<E: Engine> Circuit<E> for PolynomialMultiplier<E> {
        fn synthesize<CS: ConstraintSystem<E>>(self, cs: &mut CS) -> Result<(), SynthesisError> {
            let a = Polynomial {
                coefficients: self
                    .a
                    .iter()
                    .enumerate()
                    .map(|(i, x)| {
                        Ok(LinearCombination::zero()
                            + cs.alloc(|| format!("coeff_a {}", i), || Ok(*x))?)
                    })
                    .collect::<Result<Vec<LinearCombination<E>>, SynthesisError>>()?,
                values: Some(self.a),
            };
            let b = Polynomial {
                coefficients: self
                    .b
                    .iter()
                    .enumerate()
                    .map(|(i, x)| {
                        Ok(LinearCombination::zero()
                            + cs.alloc(|| format!("coeff_b {}", i), || Ok(*x))?)
                    })
                    .collect::<Result<Vec<LinearCombination<E>>, SynthesisError>>()?,
                values: Some(self.b),
            };
            let _prod = Polynomial::from(a)
                .alloc_product(cs.namespace(|| "product"), &Polynomial::from(b))?;
            Ok(())
        }
    }

    #[test]
    fn test_circuit() {
        let mut cs = TestConstraintSystem::<Bn256>::new();

        let circuit = PolynomialMultiplier {
            a: [1, 1, 1]
                .iter()
                .map(|i| usize_to_f::<Fr>(*i))
                .collect(),
            b: [1, 1].iter().map(|i| usize_to_f::<Fr>(*i)).collect(),
        };

        circuit.synthesize(&mut cs).expect("synthesis failed");

        if let Some(token) = cs.which_is_unsatisfied() {
            eprintln!("Error: {} is unsatisfied", token);
        }
    }
}
