use num_bigint::BigUint;
use num_traits::One;
use sapling_crypto::bellman::pairing::Engine;
use sapling_crypto::bellman::{ConstraintSystem, SynthesisError};

use std::collections::BTreeSet;

use bignat::BigNat;
use group::{SemiGroup, CircuitSemiGroup, Gadget};
use wesolowski::proof_of_exp;
use OptionExt;


// TODO (aozdemir) mod out by the <-1> subgroup.
#[derive(Clone, Debug)]
pub struct RsaGroup {
    pub g: BigUint,
    pub m: BigUint,
}

pub struct AllocatedRsaGroup<E: Engine> {
    pub g: BigNat<E>,
    pub m: BigNat<E>,
}

impl<E: Engine> AllocatedRsaGroup<E> {
    pub fn alloc_input<CS, G, M>(
        mut cs: CS,
        g: G,
        m: M,
        params: RsaGroupParams,
    ) -> Result<Self, SynthesisError>
    where
        CS: ConstraintSystem<E>,
        G: FnOnce() -> Result<BigUint, SynthesisError>,
        M: FnOnce() -> Result<BigUint, SynthesisError>,
    {
        let g = BigNat::alloc_from_nat(cs.namespace(|| "g"), g, params.limb_width, params.n_limbs)?;
        g.inputize(cs.namespace(|| "g input"))?;
        let m = BigNat::alloc_from_nat(cs.namespace(|| "m"), m, params.limb_width, params.n_limbs)?;
        m.inputize(cs.namespace(|| "m input"))?;
        Ok(Self { g, m })
    }
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

impl SemiGroup for RsaGroup {
    type Elem = BigUint;

    fn op(&self, a: &BigUint, b: &BigUint) -> BigUint {
        a * b % &self.m
    }

    fn identity(&self) -> BigUint {
        BigUint::one()
    }

    fn generator(&self) -> BigUint {
        self.g.clone()
    }
}

pub struct RsaGroupParams {
    pub limb_width: usize,
    pub n_limbs: usize,
}

pub trait RsaSetBackend<G: SemiGroup>: Sized {

    /// Create a new `RsaSet` which computes product mod `modulus`.
    fn new(group: G) -> Self;
    /// Add `n` to the set, returning whether `n` is new to the set.
    fn insert(&mut self, n: BigUint) -> bool;
    /// Remove `n` from the set, returning whether `n` was present.
    fn remove(&mut self, n: &BigUint) -> bool;
    /// The digest of the current elements (`g` to the product of the elements).
    fn digest(&self) -> G::Elem;

    /// Gets the underlying RSA group
    fn group(&self) -> &G;

    /// Add all of the `ns` to the set.
    fn insert_all<I: IntoIterator<Item = BigUint>>(&mut self, ns: I) {
        for n in ns {
            self.insert(n);
        }
    }

    /// Remove all of the `ns` from the set.
    fn remove_all<'a, I: IntoIterator<Item = &'a BigUint>>(&mut self, ns: I) where G::Elem: 'a {
        for n in ns {
            self.remove(n);
        }
    }

    fn new_with<I: IntoIterator<Item = BigUint>>(group: G, items: I) -> Self {
        let mut this = Self::new(group);
        this.insert_all(items);
        this
    }
}

/// An `RsaSetBackend` which computes products from scratch each time.
pub struct NaiveRsaSetBackend<G: SemiGroup> {
    group: G,
    elements: BTreeSet<BigUint>,
}

//impl<G: SemiGroup> std::fmt::Debug for NaiveRsaSetBackend<G> where G::Elem: std::fmt::Display {
//    fn fmt(&self, f: &mut std::fmt::Formatter) -> Result<(), std::fmt::Error> {
//        writeln!(f, "NaiveRsaSetBackend:")?;
//        for e in &self.elements {
//            writeln!(f, "\t{}", e)?;
//        }
//        Ok(())
//    }
//}

impl<G: SemiGroup> RsaSetBackend<G> for NaiveRsaSetBackend<G> where G::Elem: Ord {
    fn new(group: G) -> Self {
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

    fn digest(&self) -> G::Elem {
        self.elements
            .iter()
            .fold(self.group.generator(), |acc, elem| {
                self.group.power(&acc, &elem)
            })
    }

    fn group(&self) -> &G {
        &self.group
    }
}

pub struct RsaSet<E: Engine, Elem, CG: CircuitSemiGroup<E>, G: SemiGroup, B: RsaSetBackend<G>> where {
    pub value: Option<B>,
    pub digest: CG::Elem,
    pub group: AllocatedRsaGroup<E>,
}

impl<E: Engine, G, B> RsaSet<E, B> where G: SemiGroup, B: RsaSetBackend<G> {
    pub fn alloc<CS, F>(
        mut cs: CS,
        f: F,
        group: AllocatedRsaGroup<E>,
    ) -> Result<Self, SynthesisError>
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
            group.m.limb_width,
            group.m.limbs.len(),
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
        items: &[BigNat<E>],
    ) -> Result<Self, SynthesisError> {
        let old_value = self.value;
        let value = || -> Result<B, SynthesisError> {
            let mut value = old_value.ok_or(SynthesisError::AssignmentMissing)?;
            value.remove_all(
                items
                    .iter()
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
            items,
            challenge,
            &self.digest,
        )?;
        Ok(new_set)
    }

    pub fn insert<CS: ConstraintSystem<E>>(
        self,
        mut cs: CS,
        challenge: &BigNat<E>,
        items: &[BigNat<E>],
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
            items,
            challenge,
            &new_set.digest,
        )?;
        Ok(new_set)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use test_helpers::*;

    use std::str::FromStr;

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
            let group = AllocatedRsaGroup::new(g, m)?;
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

            let final_set =
                initial_set.remove(cs.namespace(|| "removal"), &challenge, &removed_items_vec)?;

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
