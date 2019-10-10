extern crate fnv;
extern crate num_bigint;
extern crate num_integer;
extern crate num_traits;
extern crate rand;
extern crate sapling_crypto;

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

pub mod bench {
    pub use sapling_crypto::bellman::pairing::Engine;
    pub use sapling_crypto::bellman::{
        ConstraintSystem, Index, LinearCombination, SynthesisError, Variable,
    };

    pub struct ConstraintCounter {
        n_constraints: usize,
    }

    impl ConstraintCounter {
        pub fn num_constraints(&self) -> usize {
            self.n_constraints
        }
        pub fn new() -> Self {
            Self { n_constraints: 0 }
        }
    }

    impl<E: Engine> ConstraintSystem<E> for ConstraintCounter {
        type Root = Self;
        fn alloc<F, A, AR>(&mut self, _annotation: A, _f: F) -> Result<Variable, SynthesisError>
        where
            F: FnOnce() -> Result<E::Fr, SynthesisError>,
            A: FnOnce() -> AR,
            AR: Into<String>,
        {
            Ok(Variable::new_unchecked(Index::Aux(0)))
        }
        fn alloc_input<F, A, AR>(
            &mut self,
            _annotation: A,
            _f: F,
        ) -> Result<Variable, SynthesisError>
        where
            F: FnOnce() -> Result<E::Fr, SynthesisError>,
            A: FnOnce() -> AR,
            AR: Into<String>,
        {
            Ok(Variable::new_unchecked(Index::Input(0)))
        }

        fn enforce<A, AR, LA, LB, LC>(&mut self, _annotation: A, _a: LA, _b: LB, _c: LC)
        where
            A: FnOnce() -> AR,
            AR: Into<String>,
            LA: FnOnce(LinearCombination<E>) -> LinearCombination<E>,
            LB: FnOnce(LinearCombination<E>) -> LinearCombination<E>,
            LC: FnOnce(LinearCombination<E>) -> LinearCombination<E>,
        {
            self.n_constraints += 1;
        }
        fn push_namespace<NR, N>(&mut self, _name_fn: N)
        where
            NR: Into<String>,
            N: FnOnce() -> NR,
        {
        }
        fn pop_namespace(&mut self) {}
        fn get_root(&mut self) -> &mut Self::Root {
            self
        }
    }
}

pub mod bignat;
pub mod bit;
pub mod entropy;
pub mod exp;
pub mod gadget;
pub mod group;
pub mod hash;
pub mod lazy;
pub mod mimc;
pub mod num;
pub mod poly;
pub mod set;
pub mod wesolowski;

use num_bigint::BigUint;
use sapling_crypto::bellman::pairing::ff::{PrimeField, PrimeFieldRepr};
use sapling_crypto::bellman::SynthesisError;

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
fn usize_to_f<F: PrimeField>(n: usize) -> F {
    F::from_str(&format!("{}", n)).unwrap()
}
