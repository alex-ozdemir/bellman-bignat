use num_bigint::BigUint;
use sapling_crypto::bellman::pairing::bn256::Bn256;
use sapling_crypto::bellman::pairing::ff::{PrimeField, ScalarEngine};
use sapling_crypto::bellman::pairing::Engine;
use sapling_crypto::bellman::{Circuit, ConstraintSystem, LinearCombination, SynthesisError};
use sapling_crypto::circuit::num::AllocatedNum;
use sapling_crypto::poseidon::bn256::Bn256PoseidonParams;
use sapling_crypto::poseidon::{PoseidonEngine, PoseidonHashParams, QuinticSBox};

use bignat::BigNat;
use group::{
    CircuitRsaGroup, CircuitRsaGroupParams, CircuitSemiGroup, Gadget, RsaGroup, SemiGroup,
};
use hash::{hash_to_prime, hash_to_rsa_element, helper, HashDomain};
use rsa_set::{CircuitExpSet, ExpSet, NaiveExpSet};
use std::marker::PhantomData;
use OptionExt;

pub struct Set<
    'a,
    E: PoseidonEngine<SBox = QuinticSBox<E>>,
    G: SemiGroup,
    HParams: 'a,
    Inner: ExpSet<BigUint, G = G>,
> {
    pub inner: Inner,
    pub hash_params: &'a HParams,
    pub hash_domain: HashDomain,
    // TODO revisit upon the resolution of https://github.com/rust-lang/rust/issues/64155
    pub _phant: PhantomData<E>,
}

impl<
        'a,
        E: PoseidonEngine<SBox = QuinticSBox<E>>,
        G: SemiGroup + Clone,
        HParams: 'a,
        Inner: ExpSet<BigUint, G = G> + Clone,
    > std::clone::Clone for Set<'a, E, G, HParams, Inner>
{
    fn clone(&self) -> Self {
        Self {
            inner: self.inner.clone(),
            hash_domain: self.hash_domain.clone(),
            hash_params: self.hash_params,
            _phant: self._phant,
        }
    }
}

impl<'a, HParams, E, G, Inner> ExpSet<Vec<E::Fr>> for Set<'a, E, G, HParams, Inner>
where
    HParams: PoseidonHashParams<E> + 'a,
    E: PoseidonEngine<SBox = QuinticSBox<E>, Params = HParams>,
    G: SemiGroup,
    Inner: ExpSet<BigUint, G = G>,
{
    type G = G;

    /// Add `n` to the set, returning whether `n` is new to the set.
    fn insert(&mut self, n: Vec<E::Fr>) -> bool {
        self.inner.insert(
            helper::hash_to_prime::<E>(&n, &self.hash_domain, &self.hash_params)
                .expect("Hash to prime failed")
                .0,
        )
    }
    /// Remove `n` from the set, returning whether `n` was present.
    fn remove(&mut self, n: &Vec<E::Fr>) -> bool {
        self.inner.remove(
            &helper::hash_to_prime::<E>(&n, &self.hash_domain, &self.hash_params)
                .expect("Hash to prime failed")
                .0,
        )
    }
    /// The digest of the current elements (`g` to the product of the elements).
    fn digest(&self) -> <Self::G as SemiGroup>::Elem {
        self.inner.digest()
    }

    /// Gets the underlying RSA group
    fn group(&self) -> &Self::G {
        self.inner.group()
    }
}

pub struct CircuitSet<'a, E, CG, HParams, Inner>
where
    E: PoseidonEngine<SBox = QuinticSBox<E>>,
    CG: CircuitSemiGroup,
    HParams: 'a,
    Inner: ExpSet<BigUint, G = <CG as CircuitSemiGroup>::Group>,
{
    pub value: Option<Set<'a, E, <CG as CircuitSemiGroup>::Group, HParams, Inner>>,
    pub group: CG,
    pub digest: CG::Elem,
    pub hash_params: &'a HParams,
}

impl<'a, E, CG, HParams, Inner> std::clone::Clone for CircuitSet<'a, E, CG, HParams, Inner>
where
    E: PoseidonEngine<SBox = QuinticSBox<E>>,
    CG: CircuitSemiGroup,
    HParams: 'a,
    Inner: ExpSet<BigUint, G = <CG as CircuitSemiGroup>::Group>,
{
    fn clone(&self) -> Self {
        Self {
            value: self.value.clone(),
            group: self.group.clone(),
            digest: self.digest.clone(),
            hash_params: self.hash_params,
        }
    }
}

impl<'a, E, CG, HParams, Inner> std::cmp::PartialEq for CircuitSet<'a, E, CG, HParams, Inner>
where
    E: PoseidonEngine<SBox = QuinticSBox<E>>,
    CG: CircuitSemiGroup,
    HParams: 'a,
    Inner: ExpSet<BigUint, G = <CG as CircuitSemiGroup>::Group>,
{
    fn eq(&self, other: &Self) -> bool {
        self.digest == other.digest
    }
}

impl<'a, E, CG, HParams, Inner> Gadget for CircuitSet<'a, E, CG, HParams, Inner>
where
    E: PoseidonEngine<SBox = QuinticSBox<E>>,
    CG: CircuitSemiGroup<E = E>,
    CG::Elem: Gadget<E = E, Value = <CG::Group as SemiGroup>::Elem, Access = ()>,
    HParams: 'a,
    Inner: ExpSet<BigUint, G = <CG as CircuitSemiGroup>::Group>,
{
    type E = E;
    type Value = Set<'a, E, <CG as CircuitSemiGroup>::Group, HParams, Inner>;
    type Access = CG;
    type Params = &'a HParams;
    fn alloc<CS: ConstraintSystem<Self::E>>(
        mut cs: CS,
        value: Option<&Self::Value>,
        access: Self::Access,
        params: &Self::Params,
    ) -> Result<Self, SynthesisError> {
        let digest: CG::Elem = <CG::Elem as Gadget>::alloc(
            cs.namespace(|| "digest"),
            value.map(|s| s.inner.digest()).as_ref(),
            (),
            &CG::elem_params(access.params()),
        )?;
        let group = access;
        Ok(Self {
            value: value.cloned(),
            digest,
            group,
            hash_params: params,
        })
    }
    fn wires(&self) -> Vec<LinearCombination<Self::E>> {
        unimplemented!()
    }
    fn wire_values(&self) -> Option<Vec<<Self::E as ScalarEngine>::Fr>> {
        unimplemented!()
    }
    fn value(&self) -> Option<&Self::Value> {
        unimplemented!()
    }
    fn access(&self) -> &Self::Access {
        unimplemented!()
    }
    fn params(&self) -> &Self::Params {
        unimplemented!()
    }
}

pub struct SetBenchInputs<E: Engine, S: ExpSet<BigUint>> {
    /// The initial state of the set
    pub initial_state: S,
    pub final_digest: BigUint,
    /// The items to remove from the set
    pub to_remove: Vec<Vec<E::Fr>>,
    /// The items to insert into the set
    pub to_insert: Vec<Vec<E::Fr>>,
}

impl SetBenchInputs<Bn256, NaiveExpSet<RsaGroup>> {
    pub fn from_counts(
        n_untouched: usize,
        n_removed: usize,
        n_inserted: usize,
        item_len: usize,
        hash: &Bn256PoseidonParams,
        n_bits_elem: usize,
        group: RsaGroup,
    ) -> Self {
        let untouched_items: Vec<Vec<String>> = (0..n_untouched)
            .map(|i| {
                (0..item_len)
                    .map(|j| format!("1{:06}{:03}", i, j))
                    .collect()
            })
            .collect();
        let removed_items: Vec<Vec<String>> = (0..n_removed)
            .map(|i| {
                (0..item_len)
                    .map(|j| format!("2{:06}{:03}", i, j))
                    .collect()
            })
            .collect();
        let inserted_items: Vec<Vec<String>> = (0..n_inserted)
            .map(|i| {
                (0..item_len)
                    .map(|j| format!("3{:06}{:03}", i, j))
                    .collect()
            })
            .collect();

        Self::new(
            untouched_items,
            removed_items,
            inserted_items,
            hash,
            n_bits_elem,
            group,
        )
    }
    pub fn new(
        untouched_items: Vec<Vec<String>>,
        removed_items: Vec<Vec<String>>,
        inserted_items: Vec<Vec<String>>,
        hash: &Bn256PoseidonParams,
        n_bits_elem: usize,
        group: RsaGroup,
    ) -> Self {
        let untouched: Vec<Vec<<Bn256 as ScalarEngine>::Fr>> = untouched_items
            .iter()
            .map(|i| {
                i.iter()
                    .map(|j| <Bn256 as ScalarEngine>::Fr::from_str(j).unwrap())
                    .collect()
            })
            .collect();
        let removed: Vec<Vec<<Bn256 as ScalarEngine>::Fr>> = removed_items
            .iter()
            .map(|i| {
                i.iter()
                    .map(|j| <Bn256 as ScalarEngine>::Fr::from_str(j).unwrap())
                    .collect()
            })
            .collect();
        let inserted: Vec<Vec<<Bn256 as ScalarEngine>::Fr>> = inserted_items
            .iter()
            .map(|i| {
                i.iter()
                    .map(|j| <Bn256 as ScalarEngine>::Fr::from_str(j).unwrap())
                    .collect()
            })
            .collect();
        let hash_domain = HashDomain {
            n_bits: n_bits_elem,
            n_trailing_ones: 1,
        };
        let untouched_hashes = untouched
            .iter()
            .map(|xs| helper::hash_to_rsa_element::<Bn256>(&xs, &hash_domain, hash));
        let removed_hashes = removed
            .iter()
            .map(|xs| helper::hash_to_rsa_element::<Bn256>(&xs, &hash_domain, hash));
        let inserted_hashes = inserted
            .iter()
            .map(|xs| helper::hash_to_rsa_element::<Bn256>(&xs, &hash_domain, hash));
        let final_digest = untouched_hashes
            .clone()
            .chain(inserted_hashes)
            .fold(group.g.clone(), |g, i| g.modpow(&i, &group.m));
        let set = NaiveExpSet::new_with(group, untouched_hashes.chain(removed_hashes));
        SetBenchInputs {
            initial_state: set,
            final_digest,
            to_remove: removed,
            to_insert: inserted,
        }
    }
}

#[derive(Clone)]
pub struct SetBenchParams<E: PoseidonEngine> {
    pub group: RsaGroup,
    pub limb_width: usize,
    pub n_bits_base: usize,
    pub n_bits_elem: usize,
    pub n_bits_challenge: usize,
    pub item_size: usize,
    pub n_removes: usize,
    pub n_inserts: usize,
    pub hash: E::Params,
}

pub struct SetBench<E: PoseidonEngine<SBox = QuinticSBox<E>>, S: ExpSet<BigUint>> {
    pub inputs: Option<SetBenchInputs<E, S>>,
    pub params: SetBenchParams<E>,
}

impl<E: PoseidonEngine<SBox = QuinticSBox<E>>> Circuit<E> for SetBench<E, NaiveExpSet<RsaGroup>> {
    fn synthesize<CS: ConstraintSystem<E>>(self, cs: &mut CS) -> Result<(), SynthesisError> {
        println!("Constructing Group");
        let raw_group = self
            .inputs
            .as_ref()
            .map(|s| s.initial_state.group().clone());
        let group = CircuitRsaGroup::alloc(
            cs.namespace(|| "group"),
            raw_group.as_ref(),
            (),
            &CircuitRsaGroupParams {
                limb_width: self.params.limb_width,
                n_limbs: self.params.n_bits_base / self.params.limb_width,
            },
        )?;
        group.inputize(cs.namespace(|| "group input"))?;
        println!("Constructing Set");
        let set: CircuitExpSet<E, CircuitRsaGroup<E>> = CircuitExpSet::alloc(
            cs.namespace(|| "set init"),
            self.inputs.as_ref().map(|is| &is.initial_state),
            group,
            &(),
        )?;
        set.inputize(cs.namespace(|| "initial_state input"))?;
        let hash_domain = HashDomain {
            n_bits: self.params.n_bits_elem,
            n_trailing_ones: 1,
        };
        println!("Hashing Deletions...");
        let removals = (0..self.params.n_removes)
            .map(|i| -> Result<BigNat<E>, SynthesisError> {
                let to_hash = (0..self.params.item_size)
                    .map(|j| {
                        AllocatedNum::alloc(cs.namespace(|| format!("remove {} {}", i, j)), || {
                            Ok(**self.inputs.grab()?.to_remove.get(i).grab()?.get(j).grab()?)
                        })
                    })
                    .collect::<Result<Vec<_>, _>>()?;
                hash_to_rsa_element(
                    cs.namespace(|| format!("hash remove {}", i)),
                    &to_hash,
                    self.params.limb_width,
                    &hash_domain,
                    &self.params.hash,
                )
            })
            .collect::<Result<Vec<BigNat<E>>, SynthesisError>>()?;

        println!("Hashing Insertions...");
        let insertions = (0..self.params.n_inserts)
            .map(|i| -> Result<BigNat<E>, SynthesisError> {
                let to_hash = (0..self.params.item_size)
                    .map(|j| {
                        AllocatedNum::alloc(cs.namespace(|| format!("inset {} {}", i, j)), || {
                            Ok(**self.inputs.grab()?.to_insert.get(i).grab()?.get(j).grab()?)
                        })
                    })
                    .collect::<Result<Vec<_>, _>>()?;
                hash_to_rsa_element(
                    cs.namespace(|| format!("hash insert {}", i)),
                    &to_hash,
                    self.params.limb_width,
                    &hash_domain,
                    &self.params.hash,
                )
            })
            .collect::<Result<Vec<BigNat<E>>, SynthesisError>>()?;
        let mut to_hash_to_challenge: Vec<AllocatedNum<E>> = Vec::new();
        to_hash_to_challenge.extend(
            set.digest
                .as_limbs::<CS>()
                .into_iter()
                .enumerate()
                .map(|(i, n)| {
                    n.as_sapling_allocated_num(cs.namespace(|| format!("digest hash {}", i)))
                })
                .collect::<Result<Vec<_>, _>>()?,
        );
        for i in 0..self.params.n_inserts {
            for j in 0..self.params.item_size {
                to_hash_to_challenge.push(AllocatedNum::alloc(
                    cs.namespace(|| format!("chash insert {} {}", i.clone(), j)),
                    || {
                        Ok(**self
                            .inputs
                            .as_ref()
                            .and_then(|is| is.to_insert.get(i).and_then(|iss| iss.get(j)))
                            .grab()?)
                    },
                )?)
            }
        }
        for i in 0..self.params.n_removes {
            for j in 0..self.params.item_size {
                to_hash_to_challenge.push(AllocatedNum::alloc(
                    cs.namespace(|| format!("chash remove {} {}", i.clone(), j)),
                    || {
                        Ok(**self
                            .inputs
                            .as_ref()
                            .and_then(|is| is.to_remove.get(i).and_then(|iss| iss.get(j)))
                            .grab()?)
                    },
                )?)
            }
        }

        let challenge = hash_to_prime(
            cs.namespace(|| "chash"),
            &to_hash_to_challenge,
            self.params.limb_width,
            &HashDomain {
                n_bits: self.params.n_bits_challenge,
                n_trailing_ones: 2,
            },
            &self.params.hash,
        )?;

        println!("Deleting elements");
        let reduced_set = set.remove(cs.namespace(|| "remove"), &challenge, &removals)?;

        println!("Inserting elements");
        let expanded_set =
            reduced_set.insert(cs.namespace(|| "insert"), &challenge, &insertions)?;

        let expected_digest = BigNat::alloc_from_nat(
            cs.namespace(|| "expected_digest"),
            || Ok(self.inputs.as_ref().grab()?.final_digest.clone()),
            self.params.limb_width,
            self.params.n_bits_base / self.params.limb_width,
        )?;

        println!("Verifying resulting digest");
        expanded_set
            .digest
            .equal(cs.namespace(|| "check"), &expected_digest)?;
        expanded_set.inputize(cs.namespace(|| "final_state input"))?;
        Ok(())
    }
}

#[cfg(test)]
mod test {
    // From https://en.wikipedia.org/wiki/RSA_numbers#RSA-
    #[allow(dead_code)]
    const RSA_2048: &str = "25195908475657893494027183240048398571429282126204032027777137836043662020707595556264018525880784406918290641249515082189298559149176184502808489120072844992687392807287776735971418347270261896375014971824691165077613379859095700097330459748808428401797429100642458691817195118746121515172654632282216869987549182422433637259085141865462043576798423387184774447920739934236584823824281198163815010674810451660377306056201619676256133844143603833904414952634432190114657544454178424020924616515723350778707749817125772467962926386356373289912154831438167899885040445364023527381951378636564391212010397122822120720357";
    // From my machine (openssl)
    const RSA_512: &str = "11834783464130424096695514462778870280264989938857328737807205623069291535525952722847913694296392927890261736769191982212777933726583565708193466779811767";

    use super::*;
    use std::str::FromStr;
    use test_helpers::*;

    circuit_tests! {
        small_rsa_1_swap: (SetBench {
            inputs: Some(SetBenchInputs::new(
                            [].to_vec(),
                            [
                            ["0", "1", "2", "3", "4"].iter().map(|s| s.to_string()).collect(),
                            ].to_vec(),
                            [
                            ["0", "1", "2", "3", "5"].iter().map(|s| s.to_string()).collect(),
                            ].to_vec(),
                            &Bn256PoseidonParams::new::<sapling_crypto::group_hash::Keccak256Hasher>(),
                            128,
                            RsaGroup {
                                g: BigUint::from(2usize),
                                m: BigUint::from_str(RSA_512).unwrap(),
                            },
                    )),
                    params: SetBenchParams {
                        group: RsaGroup {
                            g: BigUint::from(2usize),
                            m: BigUint::from_str(RSA_512).unwrap(),
                        },
                        limb_width: 32,
                        n_bits_elem: 128,
                        n_bits_challenge: 128,
                        n_bits_base: 512,
                        item_size: 5,
                        n_inserts: 1,
                        n_removes: 1,
                        hash: Bn256PoseidonParams::new::<sapling_crypto::group_hash::Keccak256Hasher>(),
                    },
        }, true),
        //small_rsa_5_swaps: (SetBench {
        //    inputs: Some(SetBenchInputs::new(
        //        [].to_vec(),
        //        [
        //            ["0", "1", "2", "3", "4"].iter().map(|s| s.to_string()).collect(),
        //            ["1", "1", "2", "3", "4"].iter().map(|s| s.to_string()).collect(),
        //            ["2", "1", "2", "3", "4"].iter().map(|s| s.to_string()).collect(),
        //            ["3", "1", "2", "3", "4"].iter().map(|s| s.to_string()).collect(),
        //            ["4", "1", "2", "3", "4"].iter().map(|s| s.to_string()).collect(),
        //        ].to_vec(),
        //        [
        //            ["0", "1", "2", "3", "5"].iter().map(|s| s.to_string()).collect(),
        //            ["1", "1", "2", "3", "5"].iter().map(|s| s.to_string()).collect(),
        //            ["2", "1", "2", "3", "5"].iter().map(|s| s.to_string()).collect(),
        //            ["3", "1", "2", "3", "5"].iter().map(|s| s.to_string()).collect(),
        //            ["4", "1", "2", "3", "5"].iter().map(|s| s.to_string()).collect(),
        //        ].to_vec(),
        //        &Bn256PoseidonParams::new::<sapling_crypto::group_hash::Keccak256Hasher>(),
        //        128,
        //        RsaGroup {
        //            g: BigUint::from(2usize),
        //            m: BigUint::from_str(RSA_512).unwrap(),
        //        },
        //    )),
        //    params: SetBenchParams {
        //        group: RsaGroup {
        //            g: BigUint::from(2usize),
        //            m: BigUint::from_str(RSA_512).unwrap(),
        //        },
        //        limb_width: 32,
        //        n_bits_elem: 128,
        //        n_bits_challenge: 128,
        //        n_bits_base: 512,
        //        item_size: 5,
        //        n_inserts: 5,
        //        n_removes: 5,
        //        hash: Bn256PoseidonParams::new::<sapling_crypto::group_hash::Keccak256Hasher>(),
        //    },
        //}, true),
        //full_rsa_30_swaps: (SetBench {
        //    inputs: Some(SetBenchInputs::from_counts(
        //        0,
        //        30,
        //        30,
        //        5,
        //        &Bn256PoseidonParams::new::<sapling_crypto::group_hash::Keccak256Hasher>(),
        //        2048,
        //        RsaGroup {
        //            g: BigUint::from(2usize),
        //            m: BigUint::from_str(RSA_2048).unwrap(),
        //        },
        //    )),
        //    params: SetBenchParams {
        //        group: RsaGroup {
        //            g: BigUint::from(2usize),
        //            m: BigUint::from_str(RSA_2048).unwrap(),
        //        },
        //        limb_width: 32,
        //        n_bits_elem: 2048,
        //        n_bits_challenge: 128,
        //        n_bits_base: 2048,
        //        item_size: 5,
        //        n_inserts: 30,
        //        n_removes: 30,
        //        hash: Bn256PoseidonParams::new::<sapling_crypto::group_hash::Keccak256Hasher>(),
        //    },
        //}, true),
    }
}
