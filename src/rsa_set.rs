use num_bigint::BigUint;
use sapling_crypto::bellman::{ConstraintSystem, SynthesisError};
use sapling_crypto::bellman::pairing::Engine;

use std::collections::BTreeSet;

use bignat::BigNat;
use wesolowski::proof_of_exp;
use OptionExt;

pub struct CircuitRsaGroup<E: Engine> {
    pub g: BigNat<E>,
    pub m: BigNat<E>,
}

impl<E: Engine> CircuitRsaGroup<E> {
    pub fn new(g: BigNat<E>, m: BigNat<E>) -> Result<Self, SynthesisError> {
        if g.limb_width != m.limb_width || g.limbs.len() != m.limbs.len() {
            return Err(SynthesisError::Unsatisfiable);
        }
        match (&g.value, &m.value) {
            (Some(ref g), Some(ref m)) if g >= m => {
                return Err(SynthesisError::Unsatisfiable);
            }
            _ => {}
        };
        Ok(Self { g, m })
    }
}

// TODO (aozdemir) mod out by the <-1> subgroup.
pub struct RsaGroup {
    pub g: BigUint,
    pub m: BigUint,
}

pub struct RsaGroupParams {
    pub limb_width: usize,
    pub n_limbs: usize,
}

pub trait RsaSetBackend: Sized {
    /// Create a new `RsaSet` which computes product mod `modulus`.
    fn new(group: RsaGroup) -> Self;
    /// Add `n` to the set, returning whether `n` is new to the set.
    fn insert(&mut self, n: BigUint) -> bool;
    /// Remove `n` from the set, returning whether `n` was present.
    fn remove(&mut self, n: &BigUint) -> bool;
    /// The digest of the current elements (`g` to the product of the elements).
    fn digest(&self) -> BigUint;

    /// Gets the underlying RSA group
    fn group(&self) -> &RsaGroup;

    /// Add all of the `ns` to the set.
    fn insert_all<I: IntoIterator<Item = BigUint>>(&mut self, ns: I) {
        for n in ns {
            self.insert(n);
        }
    }

    /// Remove all of the `ns` from the set.
    fn remove_all<'a, I: IntoIterator<Item = &'a BigUint>>(&mut self, ns: I) {
        for n in ns {
            self.remove(n);
        }
    }

    fn new_with<I: IntoIterator<Item = BigUint>>(group: RsaGroup, items: I) -> Self {
        let mut this = Self::new(group);
        this.insert_all(items);
        this
    }
}

/// An `RsaSet` which computes products from scratch each time.
pub struct NaiveRsaSetBackend {
    group: RsaGroup,
    elements: BTreeSet<BigUint>,
}

impl RsaSetBackend for NaiveRsaSetBackend {
    fn new(group: RsaGroup) -> Self {
        Self {
            group,
            elements: BTreeSet::new(),
        }
    }

    fn insert(&mut self, n: BigUint) -> bool {
        self.elements.insert(n)
    }

    fn remove(&mut self, n: &BigUint) -> bool {
        self.elements.remove(n)
    }

    fn digest(&self) -> BigUint {
        self.elements
            .iter()
            .fold(self.group.g.clone(), |acc, elem| {
                acc.modpow(elem, &self.group.m)
            })
    }

    fn group(&self) -> &RsaGroup {
        &self.group
    }
}

pub struct RsaSet<E: Engine, B: RsaSetBackend> {
    pub value: Option<B>,
    pub digest: BigNat<E>,
    pub group: CircuitRsaGroup<E>,
}

impl<E: Engine, B: RsaSetBackend> RsaSet<E, B> {
    pub fn alloc<CS, F>(mut cs: CS, f: F, group: CircuitRsaGroup<E>) -> Result<Self, SynthesisError>
    where
        CS: ConstraintSystem<E>,
        F: FnOnce() -> Result<B, SynthesisError>,
    {
        let mut value = None;
        let digest = BigNat::alloc_from_nat(
            cs.namespace(|| "digest"),
            // Compute the digest
            || {
                let set = f()?;
                let digest = Ok(set.digest());
                value = Some(set);
                digest
            },
            group.g.limb_width,
            group.g.limbs.len(),
        )?;
        Ok(Self {
            value,
            digest,
            group,
        })
    }

    pub fn remove<CS: ConstraintSystem<E>>(
        self,
        mut cs: CS,
        challenge: &BigNat<E>,
        items: Vec<&BigNat<E>>,
    ) -> Result<Self, SynthesisError> {
        let old_value = self.value;
        let value = || -> Result<B, SynthesisError> {
            let mut value = old_value.ok_or(SynthesisError::AssignmentMissing)?;
            value.remove_all(
                items
                    .iter()
                    .copied()
                    .map(|i| i.value.grab())
                    .collect::<Result<Vec<_>, _>>()?,
            );
            Ok(value)
        };
        let new_set = Self::alloc(cs.namespace(|| "new"), value, self.group)?;
        proof_of_exp(
            cs.namespace(|| "proof"),
            &new_set.digest,
            &new_set.group.m,
            items.into_iter().collect(),
            challenge,
            &self.digest,
        )?;
        Ok(new_set)
    }

    pub fn insert<CS: ConstraintSystem<E>>(
        self,
        mut cs: CS,
        challenge: &BigNat<E>,
        items: Vec<&BigNat<E>>,
    ) -> Result<Self, SynthesisError> {
        let old_value = self.value;
        let value = || -> Result<B, SynthesisError> {
            let mut value = old_value.ok_or(SynthesisError::AssignmentMissing)?;
            value.insert_all(
                items
                    .iter()
                    .map(|i| i.value.grab().map(|c| c.clone()))
                    .collect::<Result<Vec<_>, _>>()?,
            );
            Ok(value)
        };
        let new_set = Self::alloc(cs.namespace(|| "new"), value, self.group)?;
        proof_of_exp(
            cs.namespace(|| "proof"),
            &self.digest,
            &new_set.group.m,
            items.into_iter().collect(),
            challenge,
            &new_set.digest,
        )?;
        Ok(new_set)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use sapling_crypto::bellman::Circuit;
    use sapling_crypto::bellman::pairing::bn256::Bn256;
    use sapling_crypto::circuit::test::TestConstraintSystem;

    use std::str::FromStr;

    macro_rules! circuit_tests {
        ($($name:ident: $value:expr,)*) => {
            $(
                #[test]
                fn $name() {
                    let (circuit, is_sat) = $value;
                    let mut cs = TestConstraintSystem::<Bn256>::new();

                    circuit.synthesize(&mut cs).expect("synthesis failed");
                    println!(concat!("Constaints in {}: {}"), stringify!($name), cs.num_constraints());
                    if is_sat && !cs.is_satisfied() {
                        println!("UNSAT: {:#?}", cs.which_is_unsatisfied())
                    }

                    assert_eq!(cs.is_satisfied(), is_sat);
                }
            )*
        }
    }

    pub struct RsaRemovalInputs<'a> {
        pub g: &'a str,
        pub m: &'a str,
        pub initial_items: &'a [&'a str],
        pub removed_items: &'a [&'a str],
        pub initial_digest: &'a str,
        pub challenge: &'a str,
        pub final_digest: &'a str,
    }

    pub struct RsaRemovalParams {
        pub limb_width: usize,
        pub n_limbs_b: usize,
        pub n_limbs_e: usize,
    }

    pub struct RsaRemoval<'a> {
        inputs: Option<RsaRemovalInputs<'a>>,
        params: RsaRemovalParams,
    }

    impl<'a, E: Engine> Circuit<E> for RsaRemoval<'a> {
        fn synthesize<CS: ConstraintSystem<E>>(self, cs: &mut CS) -> Result<(), SynthesisError> {
            let group_raw = RsaGroup {
                g: BigUint::from_str(self.inputs.grab()?.g).unwrap(),
                m: BigUint::from_str(self.inputs.grab()?.m).unwrap(),
            };
            let g = BigNat::alloc_from_nat(
                cs.namespace(|| "g"),
                || Ok(group_raw.g.clone()),
                self.params.limb_width,
                self.params.n_limbs_b,
            )?;
            let challenge = BigNat::alloc_from_nat(
                cs.namespace(|| "challenge"),
                || Ok(BigUint::from_str(self.inputs.grab()?.challenge).unwrap()),
                self.params.limb_width,
                self.params.n_limbs_b,
            )?;
            let m = BigNat::alloc_from_nat(
                cs.namespace(|| "m"),
                || Ok(group_raw.m.clone()),
                self.params.limb_width,
                self.params.n_limbs_b,
            )?;
            let group = CircuitRsaGroup::new(g, m)?;
            let initial_items_vec: Vec<BigUint> = self
                .inputs
                .grab()?
                .initial_items
                .iter()
                .map(|i| BigUint::from_str(i).unwrap())
                .collect();
            let removed_items_vec: Vec<BigNat<E>> = self
                .inputs
                .grab()?
                .removed_items
                .iter()
                .enumerate()
                .map(|(i, e)| {
                    BigNat::alloc_from_nat(
                        cs.namespace(|| format!("removed item {}", i)),
                        || Ok(BigUint::from_str(e).unwrap()),
                        self.params.limb_width,
                        self.params.n_limbs_e,
                    )
                })
                .collect::<Result<Vec<BigNat<E>>, SynthesisError>>()?;
            let initial_digest = BigNat::alloc_from_nat(
                cs.namespace(|| "initial_digest"),
                || Ok(BigUint::from_str(self.inputs.grab()?.initial_digest).unwrap()),
                self.params.limb_width,
                self.params.n_limbs_b,
            )?;
            let final_digest = BigNat::alloc_from_nat(
                cs.namespace(|| "final_digest"),
                || Ok(BigUint::from_str(self.inputs.grab()?.final_digest).unwrap()),
                self.params.limb_width,
                self.params.n_limbs_b,
            )?;

            let initial_set = RsaSet::alloc(
                cs.namespace(|| "initial_set"),
                || {
                    Ok(NaiveRsaSetBackend::new_with(
                        group_raw,
                        initial_items_vec.into_iter(),
                    ))
                },
                group,
            )?;

            initial_set
                .digest
                .equal(cs.namespace(|| "initial_eq"), &initial_digest)?;

            let final_set = initial_set.remove(
                cs.namespace(|| "removal"),
                &challenge,
                removed_items_vec.iter().collect(),
            )?;

            final_set
                .digest
                .equal(cs.namespace(|| "final_eq"), &final_digest)?;
            Ok(())
        }
    }

    circuit_tests! {
        removal_init_empty: (
            RsaRemoval {
                inputs: Some(RsaRemovalInputs {
                    g: "2",
                    m: "143",
                    initial_items: &[
                    ],
                    removed_items: &[
                    ],
                    challenge: "223",
                    initial_digest: "2",
                    final_digest: "2",
                }),
                params: RsaRemovalParams {
                    limb_width: 4,
                    n_limbs_e: 2,
                    n_limbs_b: 2,
                }
            } ,
            true
        ),
        removal_init_3_remove_3: (
            RsaRemoval {
                inputs: Some(RsaRemovalInputs {
                    g: "2",
                    m: "143",
                    initial_items: &[
                        "3",
                    ],
                    removed_items: &[
                        "3",
                    ],
                    challenge: "223",
                    initial_digest: "8",
                    final_digest: "2",
                }),
                params: RsaRemovalParams {
                    limb_width: 4,
                    n_limbs_e: 2,
                    n_limbs_b: 2,
                }
            } ,
            true
        ),
        removal_init_3_remove_3_wrong: (
            RsaRemoval {
                inputs: Some(RsaRemovalInputs {
                    g: "2",
                    m: "143",
                    initial_items: &[
                        "3",
                    ],
                    removed_items: &[
                        "3",
                    ],
                    challenge: "223",
                    initial_digest: "8",
                    final_digest: "3",
                }),
                params: RsaRemovalParams {
                    limb_width: 4,
                    n_limbs_e: 2,
                    n_limbs_b: 2,
                }
            } ,
            false
        ),
        removal_init_3_5_7_remove_3: (
            RsaRemoval {
                inputs: Some(RsaRemovalInputs {
                    g: "2",
                    m: "143",
                    initial_items: &[
                        "3",
                        "5",
                        "7",
                    ],
                    removed_items: &[
                        "3",
                    ],
                    challenge: "223",
                    initial_digest: "109",
                    final_digest: "98",
                }),
                params: RsaRemovalParams {
                    limb_width: 4,
                    n_limbs_e: 2,
                    n_limbs_b: 2,
                }
            } ,
            true
        ),
        removal_init_3_5_7_remove_3_5: (
            RsaRemoval {
                inputs: Some(RsaRemovalInputs {
                    g: "2",
                    m: "143",
                    initial_items: &[
                        "3",
                        "5",
                        "7",
                    ],
                    removed_items: &[
                        "3",
                        "5",
                    ],
                    challenge: "223",
                    initial_digest: "109",
                    final_digest: "128",
                }),
                params: RsaRemovalParams {
                    limb_width: 4,
                    n_limbs_e: 2,
                    n_limbs_b: 2,
                }
            } ,
            true
        ),
    }
}
