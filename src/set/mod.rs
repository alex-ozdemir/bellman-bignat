use num_bigint::BigUint;
use sapling_crypto::bellman::pairing::ff::{PrimeField, ScalarEngine};
use sapling_crypto::bellman::pairing::Engine;
use sapling_crypto::bellman::{Circuit, ConstraintSystem, LinearCombination, SynthesisError};
use sapling_crypto::circuit::num::AllocatedNum;
use sapling_crypto::poseidon::{PoseidonEngine, QuinticSBox};

use std::fmt::{self, Debug, Formatter};
use std::marker::PhantomData;
use std::rc::Rc;

use bignat::BigNat;
use gadget::Gadget;
use group::{CircuitRsaGroup, CircuitRsaGroupParams, CircuitSemiGroup, RsaGroup, SemiGroup};
use hash::{pocklington, rsa, HashDomain};
use wesolowski::Reduced;
use OptionExt;

pub mod int_set;
pub mod merkle;
use self::int_set::{CircuitIntSet, IntSet, NaiveExpSet};

pub trait GenSet<E>
where
    E: Engine,
{
    type Digest;

    fn swap(&mut self, old: &[E::Fr], new: Vec<E::Fr>);

    /// Remove all of the `ns` from the set.
    fn swap_all<I, J>(&mut self, old: I, new: J)
    where
        I: IntoIterator<Item = Vec<E::Fr>>,
        J: IntoIterator<Item = Vec<E::Fr>>,
    {
        for (i, j) in old.into_iter().zip(new.into_iter()) {
            self.swap(i.as_slice(), j);
        }
    }

    fn digest(&self) -> Self::Digest;
}

pub struct Set<E, Inner>
where
    E: PoseidonEngine<SBox = QuinticSBox<E>>,
    Inner: IntSet,
{
    pub inner: Inner,
    pub offset: BigUint,
    pub hash_params: Rc<<E as PoseidonEngine>::Params>,
    pub hash_domain: HashDomain,
    pub limb_width: usize,
    // TODO revisit upon the resolution of https://github.com/rust-lang/rust/issues/64155
    pub _phant: PhantomData<E>,
}

impl<E, Inner> Debug for Set<E, Inner>
where
    E: PoseidonEngine<SBox = QuinticSBox<E>>,
    Inner: IntSet,
{
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        write!(f, "{:?}", self.inner)
    }
}

impl<E: PoseidonEngine<SBox = QuinticSBox<E>>, Inner: IntSet> std::clone::Clone for Set<E, Inner> {
    fn clone(&self) -> Self {
        Self {
            inner: self.inner.clone(),
            offset: self.offset.clone(),
            hash_domain: self.hash_domain.clone(),
            hash_params: self.hash_params.clone(),
            limb_width: self.limb_width.clone(),
            _phant: self._phant,
        }
    }
}

impl<E: PoseidonEngine<SBox = QuinticSBox<E>>, Inner: IntSet> Set<E, Inner> {
    fn new_with<'b>(
        group: Inner::G,
        offset: BigUint,
        hash_params: Rc<E::Params>,
        element_bits: usize,
        limb_width: usize,
        items: impl IntoIterator<Item = &'b [E::Fr]>,
    ) -> Self {
        let hash_domain = HashDomain {
            n_bits: element_bits,
            n_trailing_ones: 1,
        };
        let inner = Inner::new_with(
            group,
            items.into_iter().map(|slice| {
                rsa::helper::hash_to_rsa_element::<E>(slice, &offset, &hash_domain, limb_width, &hash_params)
            }),
        );
        Self {
            inner,
            offset: offset,
            hash_domain,
            hash_params,
            limb_width,
            _phant: PhantomData::default(),
        }
    }

    /// Gets the underlying RSA group
    pub fn group(&self) -> &Inner::G {
        self.inner.group()
    }

    /// Add `n` to the set, returning whether `n` is new to the set.
    fn insert(&mut self, n: Vec<E::Fr>) -> bool {
        let x = rsa::helper::hash_to_rsa_element::<E>(
            &n,
            &self.offset,
            &self.hash_domain,
            self.limb_width,
            &self.hash_params,
        );
        self.inner.insert(x)
    }
    /// Remove `n` from the set, returning whether `n` was present.
    fn remove(&mut self, n: &[E::Fr]) -> bool {
        let x = rsa::helper::hash_to_rsa_element::<E>(
            &n,
            &self.offset,
            &self.hash_domain,
            self.limb_width,
            &self.hash_params,
        );
        self.inner.remove(&x)
    }

    pub fn remove_all<'b, I: IntoIterator<Item = &'b [E::Fr]>>(&mut self, ns: I) -> bool
    where
        <Inner::G as SemiGroup>::Elem: 'b,
    {
        let mut all_present = true;
        for n in ns {
            all_present &= self.remove(n);
        }
        all_present
    }

    pub fn insert_all<I: IntoIterator<Item = Vec<E::Fr>>>(&mut self, ns: I) -> bool {
        let mut all_absent = true;
        for n in ns {
            all_absent &= self.insert(n);
        }
        all_absent
    }
}

impl<E, Inner> GenSet<E> for Set<E, Inner>
where
    E: PoseidonEngine<SBox = QuinticSBox<E>>,
    Inner: IntSet,
{
    type Digest = <Inner::G as SemiGroup>::Elem;

    fn swap(&mut self, old: &[E::Fr], new: Vec<E::Fr>) {
        self.remove(old);
        self.insert(new);
    }

    /// The digest of the current elements (`g` to the product of the elements).
    fn digest(&self) -> <Inner::G as SemiGroup>::Elem {
        self.inner.digest()
    }
}

pub struct CircuitSetParams<HParams> {
    hash: Rc<HParams>,
    n_bits: usize,
    limb_width: usize,
}

impl<HParams> CircuitSetParams<HParams> {
    fn hash_domain(&self) -> HashDomain {
        HashDomain {
            n_bits: self.n_bits,
            n_trailing_ones: 1,
        }
    }
}

impl<HParams> std::clone::Clone for CircuitSetParams<HParams> {
    fn clone(&self) -> Self {
        Self {
            hash: self.hash.clone(),
            n_bits: self.n_bits,
            limb_width: self.limb_width,
        }
    }
}

pub struct CircuitSet<E, CG, Inner>
where
    E: PoseidonEngine<SBox = QuinticSBox<E>>,
    CG: CircuitSemiGroup<E = E> + Gadget<E = E, Value = <CG as CircuitSemiGroup>::Group>,
    CG::Elem: Gadget<E = E, Value = <CG::Group as SemiGroup>::Elem, Access = ()>,
    Inner: IntSet<G = <CG as CircuitSemiGroup>::Group>,
{
    pub value: Option<Set<E, Inner>>,
    pub offset: Reduced<E>,
    pub access: (CG, BigNat<E>),
    pub inner: CircuitIntSet<E, CG, Inner>,
    pub params: CircuitSetParams<E::Params>,
}


impl<E, CG, Inner> std::clone::Clone for CircuitSet<E, CG, Inner>
where
    E: PoseidonEngine<SBox = QuinticSBox<E>>,
    CG: CircuitSemiGroup<E = E> + Gadget<E = E, Value = <CG as CircuitSemiGroup>::Group>,
    CG::Elem: Gadget<E = E, Value = <CG::Group as SemiGroup>::Elem, Access = ()>,
    Inner: IntSet<G = <CG as CircuitSemiGroup>::Group>,
{
    fn clone(&self) -> Self {
        Self {
            value: self.value.clone(),
            inner: self.inner.clone(),
            params: self.params.clone(),
            access: self.access.clone(),
            offset: self.offset.clone(),
        }
    }
}

impl<E, CG, Inner> Gadget for CircuitSet<E, CG, Inner>
where
    E: PoseidonEngine<SBox = QuinticSBox<E>>,
    CG: CircuitSemiGroup<E = E> + Gadget<E = E, Value = <CG as CircuitSemiGroup>::Group>,
    CG::Elem: Gadget<E = E, Value = <CG::Group as SemiGroup>::Elem, Access = ()>,
    Inner: IntSet<G = <CG as CircuitSemiGroup>::Group>,
{
    type E = E;
    type Value = Set<E, Inner>;
    /// Access is the circuit group and the challenge.
    type Access = (CG, BigNat<E>);
    type Params = CircuitSetParams<E::Params>;
    fn alloc<CS: ConstraintSystem<Self::E>>(
        mut cs: CS,
        value: Option<&Self::Value>,
        access: Self::Access,
        params: &Self::Params,
    ) -> Result<Self, SynthesisError> {
        let inner = CircuitIntSet::alloc(
            cs.namespace(|| "int set"),
            value.as_ref().map(|s| &s.inner),
            access.0.clone(),
            &(),
        )?;
        Ok(Self {
            value: value.cloned(),
            inner,
            offset: rsa::allocate_offset(cs.namespace(|| "hash offset % l"), &access.1, params.n_bits)?,
            access,
            params: params.clone(),
        })
    }
    fn wires(&self) -> Vec<LinearCombination<Self::E>> {
        self.inner.wires()
    }
    fn wire_values(&self) -> Option<Vec<<Self::E as ScalarEngine>::Fr>> {
        self.inner.wire_values()
    }
    fn value(&self) -> Option<&Self::Value> {
        self.value.as_ref()
    }
    fn access(&self) -> &Self::Access {
        &self.access
    }
    fn params(&self) -> &Self::Params {
        &self.params
    }
}

impl<E, CG, Inner> CircuitSet<E, CG, Inner>
where
    E: PoseidonEngine<SBox = QuinticSBox<E>>,
    CG: CircuitSemiGroup<E = E> + Gadget<E = E, Value = <CG as CircuitSemiGroup>::Group>,
    CG::Elem: Gadget<E = E, Value = <CG::Group as SemiGroup>::Elem, Access = ()>,
    Inner: IntSet<G = <CG as CircuitSemiGroup>::Group>,
{
    pub fn remove<'b, CS: ConstraintSystem<E>>(
        self,
        mut cs: CS,
        items: impl IntoIterator<Item = &'b [AllocatedNum<E>]> + Clone,
    ) -> Result<Self, SynthesisError> {
        let removals = items
            .clone()
            .into_iter()
            .enumerate()
            .map(|(i, slice)| -> Result<Reduced<E>, SynthesisError> {
                rsa::hash_to_modded_rsa_element(
                    cs.namespace(|| format!("hash {}", i)),
                    &slice,
                    self.params.limb_width,
                    &self.params.hash_domain(),
                    &self.offset,
                    &self.access.1,
                    &self.params.hash,
                )
            })
            .collect::<Result<Vec<Reduced<E>>, SynthesisError>>()?;
        let inner = self.inner.remove(
            cs.namespace(|| "int removals"),
            &self.access.1,
            &removals,
        )?;
        let value = self.value.as_ref().and_then(|v| {
            let is: Option<Vec<Vec<E::Fr>>> = items
                .into_iter()
                .map(|i| i.iter().map(|n| n.get_value()).collect::<Option<Vec<_>>>())
                .collect::<Option<Vec<_>>>();
            is.map(|is| {
                let mut v = v.clone();
                assert!(v.remove_all(is.iter().map(Vec::as_slice)));
                v
            })
        });
        Ok(Self {
            value,
            inner,
            params: self.params.clone(),
            access: self.access.clone(),
            offset: self.offset.clone(),
        })
    }

    pub fn insert<'b, CS: ConstraintSystem<E>>(
        self,
        mut cs: CS,
        items: impl IntoIterator<Item = &'b [AllocatedNum<E>]> + Clone,
    ) -> Result<Self, SynthesisError> {
        let insertions = items
            .clone()
            .into_iter()
            .enumerate()
            .map(|(i, slice)| -> Result<Reduced<E>, SynthesisError> {
                rsa::hash_to_modded_rsa_element(
                    cs.namespace(|| format!("hash {}", i)),
                    &slice,
                    self.params.limb_width,
                    &self.params.hash_domain(),
                    &self.offset,
                    &self.access.1,
                    &self.params.hash,
                )
            })
            .collect::<Result<Vec<Reduced<E>>, SynthesisError>>()?;
        let inner = self.inner.insert(
            cs.namespace(|| "int insertions"),
            &self.access.1,
            &insertions,
        )?;
        let value = self.value.as_ref().and_then(|v| {
            let is: Option<Vec<Vec<E::Fr>>> = items
                .into_iter()
                .map(|i| i.iter().map(|n| n.get_value()).collect::<Option<Vec<_>>>())
                .collect::<Option<Vec<_>>>();
            is.map(|is| {
                let mut v = v.clone();
                v.insert_all(is.into_iter());
                v
            })
        });
        Ok(Self {
            value,
            inner,
            params: self.params.clone(),
            access: self.access.clone(),
            offset: self.offset.clone(),
        })
    }

    fn swap_all<'b, CS: ConstraintSystem<E>>(
        self,
        mut cs: CS,
        removed_items: impl IntoIterator<Item = &'b [AllocatedNum<E>]> + Clone,
        inserted_items: impl IntoIterator<Item = &'b [AllocatedNum<E>]> + Clone,
    ) -> Result<Self, SynthesisError> {
        let without = self.remove(cs.namespace(|| "remove"), removed_items)?;
        without.insert(cs.namespace(|| "insert"), inserted_items)
    }
}

pub struct SetBenchInputs<E, Inner>
where
    E: PoseidonEngine<SBox = QuinticSBox<E>>,
    Inner: IntSet,
{
    /// The initial state of the set
    pub initial_state: Set<E, Inner>,
    pub final_digest: BigUint,
    /// The items to remove from the set
    pub to_remove: Vec<Vec<E::Fr>>,
    /// The items to insert into the set
    pub to_insert: Vec<Vec<E::Fr>>,
}

impl<E, Inner> SetBenchInputs<E, Inner>
where
    E: PoseidonEngine<SBox = QuinticSBox<E>>,
    Inner: IntSet<G = RsaGroup>,
{
    pub fn from_counts(
        n_untouched: usize,
        n_removed: usize,
        n_inserted: usize,
        item_len: usize,
        hash: Rc<E::Params>,
        n_bits_elem: usize,
        limb_width: usize,
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
            limb_width,
            group,
        )
    }
    pub fn new(
        untouched_items: Vec<Vec<String>>,
        removed_items: Vec<Vec<String>>,
        inserted_items: Vec<Vec<String>>,
        hash: Rc<E::Params>,
        n_bits_elem: usize,
        limb_width: usize,
        group: RsaGroup,
    ) -> Self {
        let untouched: Vec<Vec<E::Fr>> = untouched_items
            .iter()
            .map(|i| i.iter().map(|j| E::Fr::from_str(j).unwrap()).collect())
            .collect();
        let removed: Vec<Vec<E::Fr>> = removed_items
            .iter()
            .map(|i| i.iter().map(|j| E::Fr::from_str(j).unwrap()).collect())
            .collect();
        let inserted: Vec<Vec<E::Fr>> = inserted_items
            .iter()
            .map(|i| i.iter().map(|j| E::Fr::from_str(j).unwrap()).collect())
            .collect();
        let hash_domain = HashDomain {
            n_bits: n_bits_elem,
            n_trailing_ones: 1,
        };
        let offset = rsa::offset(n_bits_elem);
        let untouched_hashes = untouched
            .iter()
            .map(|xs| rsa::helper::hash_to_rsa_element::<E>(&xs, &offset, &hash_domain, limb_width, &hash));
        let inserted_hashes = inserted
            .iter()
            .map(|xs| rsa::helper::hash_to_rsa_element::<E>(&xs, &offset, &hash_domain, limb_width, &hash));
        let final_digest = untouched_hashes
            .clone()
            .chain(inserted_hashes)
            .fold(group.g.clone(), |g, i| g.modpow(&i, &group.m));
        let initial_state = Set::new_with(
            group,
            offset,
            hash,
            n_bits_elem,
            limb_width,
            untouched.iter().chain(&removed).map(|v| v.as_slice()),
        );
        SetBenchInputs {
            initial_state,
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
    pub hash: Rc<E::Params>,
    pub verbose: bool,
}

pub struct SetBench<E, Inner>
where
    E: PoseidonEngine<SBox = QuinticSBox<E>>,
    Inner: IntSet,
{
    pub inputs: Option<SetBenchInputs<E, Inner>>,
    pub params: SetBenchParams<E>,
}

impl<E> Circuit<E> for SetBench<E, NaiveExpSet<RsaGroup>>
where
    E: PoseidonEngine<SBox = QuinticSBox<E>>,
{
    fn synthesize<CS: ConstraintSystem<E>>(self, cs: &mut CS) -> Result<(), SynthesisError> {
        if self.params.verbose {
            println!("Allocating Deletions...");
        }
        let removals = (0..self.params.n_removes)
            .map(|i| {
                (0..self.params.item_size)
                    .map(|j| {
                        AllocatedNum::alloc(cs.namespace(|| format!("remove {} {}", i, j)), || {
                            Ok(**self.inputs.grab()?.to_remove.get(i).grab()?.get(j).grab()?)
                        })
                    })
                    .collect::<Result<Vec<_>, _>>()
            })
            .collect::<Result<Vec<Vec<AllocatedNum<E>>>, SynthesisError>>()?;

        if self.params.verbose {
            println!("Allocating Insertions...");
        }
        let insertions = (0..self.params.n_inserts)
            .map(|i| {
                (0..self.params.item_size)
                    .map(|j| {
                        AllocatedNum::alloc(cs.namespace(|| format!("insert {} {}", i, j)), || {
                            Ok(**self.inputs.grab()?.to_insert.get(i).grab()?.get(j).grab()?)
                        })
                    })
                    .collect::<Result<Vec<_>, _>>()
            })
            .collect::<Result<Vec<Vec<AllocatedNum<E>>>, SynthesisError>>()?;

        let expected_digest = BigNat::alloc_from_nat(
            cs.namespace(|| "expected_digest"),
            || Ok(self.inputs.as_ref().grab()?.final_digest.clone()),
            self.params.limb_width,
            self.params.n_bits_base / self.params.limb_width,
        )?;

        if self.params.verbose {
            println!("Hashing everything");
        }
        let mut to_hash_to_challenge: Vec<AllocatedNum<E>> = Vec::new();
        to_hash_to_challenge.extend(insertions.iter().flat_map(|i| i.iter().cloned()));
        to_hash_to_challenge.extend(removals.iter().flat_map(|i| i.iter().cloned()));
        let challenge = pocklington::hash_to_pocklington_prime(
            cs.namespace(|| "chash"),
            &to_hash_to_challenge,
            self.params.limb_width,
            self.params.n_bits_challenge,
            &self.params.hash,
        )?;

        if self.params.verbose {
            println!("Constructing Group");
        }
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

        if self.params.verbose {
            println!("Constructing Set");
        }
        let set: CircuitSet<E, CircuitRsaGroup<E>, NaiveExpSet<RsaGroup>> = CircuitSet::alloc(
            cs.namespace(|| "set init"),
            self.inputs.as_ref().map(|is| &is.initial_state),
            (group, challenge),
            &CircuitSetParams {
                hash: self.params.hash.clone(),
                n_bits: self.params.n_bits_elem,
                limb_width: self.params.limb_width,
            },
        )?;
        set.inputize(cs.namespace(|| "initial_state input"))?;

        if self.params.verbose {
            println!("Swapping elements");
        }
        let new_set = set.swap_all(
            cs.namespace(|| "swap"),
            removals.iter().map(Vec::as_slice),
            insertions.iter().map(Vec::as_slice),
        )?;

        if self.params.verbose {
            println!("Verifying resulting digest");
        }
        new_set
            .inner
            .digest
            .equal(cs.namespace(|| "check"), &expected_digest)?;
        new_set.inputize(cs.namespace(|| "final_state input"))?;
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
    use sapling_crypto::group_hash::Keccak256Hasher;
    use sapling_crypto::poseidon::bn256::Bn256PoseidonParams;
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
                            Rc::new(Bn256PoseidonParams::new::<Keccak256Hasher>()),
                            128,
                            32,
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
                        hash: Rc::new(Bn256PoseidonParams::new::<Keccak256Hasher>()),
                        verbose: true,
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
