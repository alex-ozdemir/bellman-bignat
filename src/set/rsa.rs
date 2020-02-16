use num_bigint::BigUint;
use sapling_crypto::bellman::pairing::ff::{PrimeField, ScalarEngine};
use sapling_crypto::bellman::pairing::Engine;
use sapling_crypto::bellman::{Circuit, ConstraintSystem, LinearCombination, SynthesisError};
use sapling_crypto::circuit::num::AllocatedNum;

use std::fmt::{self, Debug, Formatter};

use group::{
    CircuitRsaGroupParams, CircuitRsaQuotientGroup, CircuitSemiGroup, RsaQuotientGroup, SemiGroup,
};
use hash::circuit::{CircuitHasher, MaybeHashed};
use hash::Hasher;
use hash::{division_intractable as di, pocklington, HashDomain};
use mp::bignat::BigNat;
use set::int_set::{CircuitIntSet, IntSet};
use set::{CircuitGenSet, GenSet};
use util::gadget::Gadget;
use util::verbose::in_verbose_mode;
use wesolowski::Reduced;
use CResult;
use OptionExt;

#[derive(Derivative)]
#[derivative(Clone(bound = ""))]
pub struct Set<H, Inner>
where
    H: Hasher,
    Inner: IntSet,
{
    pub inner: Inner,
    pub offset: BigUint,
    pub hasher: H,
    pub hash_domain: HashDomain,
    pub limb_width: usize,
}

impl<H, Inner> Debug for Set<H, Inner>
where
    H: Hasher,
    Inner: IntSet,
{
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        write!(f, "{:?}", self.inner)
    }
}

impl<H: Hasher, Inner: IntSet> Set<H, Inner> {
    pub fn new_with(
        group: Inner::G,
        offset: BigUint,
        hasher: H,
        element_bits: usize,
        limb_width: usize,
        items: &Vec<Vec<<H as Hasher>::F>>,
    ) -> Self {
        let hash_domain = HashDomain {
            n_bits: element_bits,
            n_trailing_ones: 1,
        };
        use rayon::prelude::*;
        if in_verbose_mode() {
            println!("Hashing");
        }
        let hashed = items
            .par_iter()
            .map(|slice| {
                di::helper::di_hash::<H>(&slice, &offset, &hash_domain, limb_width, &hasher)
            })
            .collect::<Vec<_>>();

        let inner = Inner::new_with(group, hashed);
        Self {
            inner,
            offset: offset,
            hash_domain,
            hasher,
            limb_width,
        }
    }

    /// Gets the underlying RSA group
    pub fn group(&self) -> &Inner::G {
        self.inner.group()
    }

    /// Add `n` to the set.
    pub fn insert(&mut self, n: Vec<H::F>) {
        let x = di::helper::di_hash::<H>(
            &n,
            &self.offset,
            &self.hash_domain,
            self.limb_width,
            &self.hasher,
        );
        self.inner.insert(x)
    }
    /// Remove `n` from the set, returning whether `n` was present.
    pub fn remove(&mut self, n: &[H::F]) -> bool {
        let x = di::helper::di_hash::<H>(
            &n,
            &self.offset,
            &self.hash_domain,
            self.limb_width,
            &self.hasher,
        );
        self.inner.remove(&x)
    }

    pub fn remove_all<'b, I: IntoIterator<Item = &'b [H::F]>>(&mut self, ns: I) -> bool
    where
        <Inner::G as SemiGroup>::Elem: 'b,
    {
        let mut all_present = true;
        for n in ns {
            all_present &= self.remove(n);
        }
        all_present
    }

    pub fn insert_all<I: IntoIterator<Item = Vec<H::F>>>(&mut self, ns: I) {
        for n in ns {
            self.insert(n);
        }
    }
}

impl<H, Inner> GenSet<H::F> for Set<H, Inner>
where
    H: Hasher,
    Inner: IntSet,
{
    type Digest = <Inner::G as SemiGroup>::Elem;

    fn swap(&mut self, old: &[H::F], new: Vec<H::F>) {
        self.insert(new);
        self.remove(old);
    }

    /// The digest of the current elements (`g` to the product of the elements).
    fn digest(&mut self) -> <Inner::G as SemiGroup>::Elem {
        self.inner.digest()
    }
}

#[derive(Clone)]
pub struct CircuitSetParams<H> {
    pub hasher: H,
    pub n_bits: usize,
    pub limb_width: usize,
}

impl<H> CircuitSetParams<H> {
    fn hash_domain(&self) -> HashDomain {
        HashDomain {
            n_bits: self.n_bits,
            n_trailing_ones: 1,
        }
    }
}

#[derive(Derivative)]
#[derivative(Clone(bound = ""))]
pub struct CircuitSet<E, H, CG, Inner>
where
    E: Engine,
    H: CircuitHasher<E = E> + Hasher<F = E::Fr>,
    CG: CircuitSemiGroup<E = E> + Gadget<E = E, Value = <CG as CircuitSemiGroup>::Group>,
    CG::Elem: Gadget<E = E, Value = <CG::Group as SemiGroup>::Elem, Access = ()>,
    Inner: IntSet<G = <CG as CircuitSemiGroup>::Group>,
{
    pub value: Option<Set<H, Inner>>,
    pub offset: Reduced<E>,
    pub access: (CG, BigNat<E>),
    pub inner: CircuitIntSet<E, CG, Inner>,
    pub params: CircuitSetParams<H>,
}

impl<E, H, CG, Inner> Gadget for CircuitSet<E, H, CG, Inner>
where
    E: Engine,
    H: CircuitHasher<E = E> + Hasher<F = E::Fr>,
    CG: CircuitSemiGroup<E = E> + Gadget<E = E, Value = <CG as CircuitSemiGroup>::Group>,
    CG::Elem: Gadget<E = E, Value = <CG::Group as SemiGroup>::Elem, Access = ()>,
    Inner: IntSet<G = <CG as CircuitSemiGroup>::Group>,
{
    type E = E;
    type Value = Set<H, Inner>;
    /// Access is the circuit group and the challenge.
    type Access = (CG, BigNat<E>);
    type Params = CircuitSetParams<H>;
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
            offset: di::allocate_offset(
                cs.namespace(|| "hash offset % l"),
                &access.1,
                params.n_bits,
            )?,
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

impl<E, H, CG, Inner> CircuitSet<E, H, CG, Inner>
where
    E: Engine,
    H: CircuitHasher<E = E> + Hasher<F = E::Fr>,
    CG: CircuitSemiGroup<E = E> + Gadget<E = E, Value = <CG as CircuitSemiGroup>::Group>,
    CG::Elem: Gadget<E = E, Value = <CG::Group as SemiGroup>::Elem, Access = ()>,
    Inner: IntSet<G = <CG as CircuitSemiGroup>::Group>,
{
    pub fn remove<'b, CS: ConstraintSystem<E>>(
        self,
        mut cs: CS,
        items: &mut Vec<MaybeHashed<E>>,
    ) -> Result<Self, SynthesisError> {
        let removals = items
            .into_iter()
            .enumerate()
            .map(|(i, mut input)| -> Result<Reduced<E>, SynthesisError> {
                di::modded_di_hash(
                    cs.namespace(|| format!("hash {}", i)),
                    &mut input,
                    self.params.limb_width,
                    &self.params.hash_domain(),
                    &self.offset,
                    &self.access.1,
                    &self.params.hasher,
                )
            })
            .collect::<Result<Vec<Reduced<E>>, SynthesisError>>()?;
        let inner =
            self.inner
                .remove(cs.namespace(|| "int removals"), &self.access.1, &removals)?;
        let value = self.value.as_ref().and_then(|v| {
            let is: Option<Vec<Vec<E::Fr>>> = items
                .into_iter()
                .map(|i| {
                    i.values
                        .iter()
                        .map(|n| n.get_value())
                        .collect::<Option<Vec<_>>>()
                })
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
        items: &mut Vec<MaybeHashed<E>>,
    ) -> Result<Self, SynthesisError> {
        let insertions = items
            .into_iter()
            .enumerate()
            .map(|(i, mut slice)| -> Result<Reduced<E>, SynthesisError> {
                di::modded_di_hash(
                    cs.namespace(|| format!("hash {}", i)),
                    &mut slice,
                    self.params.limb_width,
                    &self.params.hash_domain(),
                    &self.offset,
                    &self.access.1,
                    &self.params.hasher,
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
                .map(|i| {
                    i.values
                        .iter()
                        .map(|n| n.get_value())
                        .collect::<Option<Vec<_>>>()
                })
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
}

impl<E, H, CG, Inner> CircuitGenSet for CircuitSet<E, H, CG, Inner>
where
    E: Engine,
    H: CircuitHasher<E = E> + Hasher<F = E::Fr>,
    CG: CircuitSemiGroup<E = E> + Gadget<E = E, Value = <CG as CircuitSemiGroup>::Group>,
    CG::Elem: Gadget<E = E, Value = <CG::Group as SemiGroup>::Elem, Access = ()>,
    Inner: IntSet<G = <CG as CircuitSemiGroup>::Group>,
{
    type E = E;
    fn swap_all<CS: ConstraintSystem<Self::E>>(
        self,
        mut cs: CS,
        mut removed_items: Vec<MaybeHashed<Self::E>>,
        mut inserted_items: Vec<MaybeHashed<Self::E>>,
    ) -> CResult<Self> {
        let with = self.insert(cs.namespace(|| "insert"), &mut inserted_items)?;
        let without = with.remove(cs.namespace(|| "remove"), &mut removed_items)?;
        Ok(without)
    }
    fn verify_swap_all<CS: ConstraintSystem<Self::E>>(
        self,
        mut cs: CS,
        mut removed_items: Vec<MaybeHashed<Self::E>>,
        mut inserted_items: Vec<MaybeHashed<Self::E>>,
        other: Self,
    ) -> CResult<()> {
        let with = self.insert(cs.namespace(|| "insert"), &mut inserted_items)?;
        let also_with = other.insert(cs.namespace(|| "rev insert"), &mut removed_items)?;
        Gadget::assert_equal(
            cs.namespace(|| "check"),
            &with.inner.digest,
            &also_with.inner.digest,
        )?;
        Ok(())
    }
}

pub struct SetBenchInputs<H, Inner>
where
    H: Hasher,
    Inner: IntSet,
{
    /// The initial state of the set
    pub initial_state: Set<H, Inner>,
    pub final_state: Set<H, Inner>,
    /// The items to remove from the set
    pub to_remove: Vec<Vec<H::F>>,
    /// The items to insert into the set
    pub to_insert: Vec<Vec<H::F>>,
}

impl<H, Inner> SetBenchInputs<H, Inner>
where
    H: Hasher,
    Inner: IntSet<G = RsaQuotientGroup>,
{
    /// Creates an input to the set benchmark in which fixed numbers of items are present but
    /// unmodified, a fixed number of items are removed, and a fixed number are added.
    pub fn from_counts(
        n_untouched: usize,
        n_removed: usize,
        n_inserted: usize,
        item_len: usize,
        hasher: H,
        n_bits_elem: usize,
        limb_width: usize,
        group: RsaQuotientGroup,
    ) -> Self {
        use rayon::prelude::*;
        let untouched_items: Vec<Vec<String>> = (0..n_untouched)
            .into_par_iter()
            .map(|i| {
                (0..item_len)
                    .map(|j| format!("1{:06}{:03}", i, j))
                    .collect()
            })
            .collect();
        let removed_items: Vec<Vec<String>> = (0..n_removed)
            .into_par_iter()
            .map(|i| {
                (0..item_len)
                    .map(|j| format!("2{:06}{:03}", i, j))
                    .collect()
            })
            .collect();
        let inserted_items: Vec<Vec<String>> = (0..n_inserted)
            .into_par_iter()
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
            hasher,
            n_bits_elem,
            limb_width,
            group,
        )
    }
    pub fn new(
        untouched_items: Vec<Vec<String>>,
        removed_items: Vec<Vec<String>>,
        inserted_items: Vec<Vec<String>>,
        hasher: H,
        n_bits_elem: usize,
        limb_width: usize,
        group: RsaQuotientGroup,
    ) -> Self {
        use rayon::prelude::*;
        let untouched: Vec<Vec<H::F>> = untouched_items
            .par_iter()
            .map(|i| i.iter().map(|j| H::F::from_str(j).unwrap()).collect())
            .collect();
        let removed: Vec<Vec<H::F>> = removed_items
            .par_iter()
            .map(|i| i.iter().map(|j| H::F::from_str(j).unwrap()).collect())
            .collect();
        let inserted: Vec<Vec<H::F>> = inserted_items
            .par_iter()
            .map(|i| i.iter().map(|j| H::F::from_str(j).unwrap()).collect())
            .collect();
        let offset = di::offset(n_bits_elem);
        if in_verbose_mode() {
            println!("Constructing common state");
        }
        let mut initial_state =
            Set::new_with(group, offset, hasher, n_bits_elem, limb_width, &untouched);
        // We compute digests unecessarily to force evaluation.
        if in_verbose_mode() {
            println!("Computing common digest");
        }
        initial_state.digest();
        if in_verbose_mode() {
            println!("Adding initial items");
        }
        let mut final_state = initial_state.clone();
        initial_state.insert_all(removed.clone());
        initial_state.digest();
        if in_verbose_mode() {
            println!("Adding final items");
        }
        final_state.insert_all(inserted.clone());
        final_state.digest();
        if in_verbose_mode() {
            println!("Done adding final items");
        }
        SetBenchInputs {
            initial_state,
            final_state,
            to_remove: removed,
            to_insert: inserted,
        }
    }
}

#[derive(Clone)]
pub struct SetBenchParams<H> {
    pub group: RsaQuotientGroup,
    pub limb_width: usize,
    pub n_bits_base: usize,
    pub n_bits_elem: usize,
    pub n_bits_challenge: usize,
    pub item_size: usize,
    pub n_removes: usize,
    pub n_inserts: usize,
    pub hasher: H,
    pub verbose: bool,
}

pub struct SetBench<H, Inner>
where
    H: Hasher,
    Inner: IntSet,
{
    pub inputs: Option<SetBenchInputs<H, Inner>>,
    pub params: SetBenchParams<H>,
}

impl<E, Inner, H> Circuit<E> for SetBench<H, Inner>
where
    E: Engine,
    H: Hasher<F = E::Fr> + CircuitHasher<E = E>,
    Inner: IntSet<G = RsaQuotientGroup>,
{
    fn synthesize<CS: ConstraintSystem<E>>(mut self, cs: &mut CS) -> Result<(), SynthesisError> {
        if self.params.verbose {
            println!("Allocating Deletions...");
        }
        let removals = (0..self.params.n_removes)
            .map(|i| {
                let mut cs = cs.namespace(|| format!("init removals {}", i));
                let values = (0..self.params.item_size)
                    .map(|j| {
                        AllocatedNum::alloc(cs.namespace(|| format!("alloc {} {}", i, j)), || {
                            Ok(**self.inputs.grab()?.to_remove.get(i).grab()?.get(j).grab()?)
                        })
                    })
                    .collect::<Result<Vec<_>, _>>()?;
                let hash = self
                    .params
                    .hasher
                    .allocate_hash(cs.namespace(|| format!("hash {}", i)), &values)?;
                Ok(MaybeHashed::new(values, hash))
            })
            .collect::<Result<Vec<MaybeHashed<E>>, SynthesisError>>()?;

        if self.params.verbose {
            println!("Allocating Insertions...");
        }
        let insertions = (0..self.params.n_inserts)
            .map(|i| {
                let mut cs = cs.namespace(|| format!("init insertions {}", i));
                let values = (0..self.params.item_size)
                    .map(|j| {
                        AllocatedNum::alloc(cs.namespace(|| format!("alloc {} {}", i, j)), || {
                            Ok(**self.inputs.grab()?.to_insert.get(i).grab()?.get(j).grab()?)
                        })
                    })
                    .collect::<Result<Vec<_>, _>>()?;
                let hash = self
                    .params
                    .hasher
                    .allocate_hash(cs.namespace(|| format!("hash {}", i)), &values)?;
                Ok(MaybeHashed::new(values, hash))
            })
            .collect::<Result<Vec<MaybeHashed<E>>, SynthesisError>>()?;

        let limb_width = self.params.limb_width;
        let n_bits_base = self.params.n_bits_base;
        let expected_initial_digest = BigNat::alloc_from_nat(
            cs.namespace(|| "expected_initial_digest"),
            || {
                Ok(self
                    .inputs
                    .as_mut()
                    .ok_or(SynthesisError::AssignmentMissing)?
                    .initial_state
                    .digest())
            },
            limb_width,
            n_bits_base / limb_width,
        )?;
        let expected_final_digest = BigNat::alloc_from_nat(
            cs.namespace(|| "expected_final_digest"),
            || {
                Ok(self
                    .inputs
                    .as_mut()
                    .ok_or(SynthesisError::AssignmentMissing)?
                    .final_state
                    .digest())
            },
            limb_width,
            n_bits_base / limb_width,
        )?;

        if self.params.verbose {
            println!("Constructing the challenge");
        }

        let challenge = {
            let mut to_hash_to_challenge: Vec<AllocatedNum<E>> = Vec::new();
            to_hash_to_challenge.extend(
                expected_initial_digest
                    .as_limbs::<CS>()
                    .into_iter()
                    .enumerate()
                    .map(|(i, n)| {
                        n.as_sapling_allocated_num(
                            cs.namespace(|| format!("initial digest hash {}", i)),
                        )
                    })
                    .collect::<Result<Vec<_>, _>>()?,
            );
            to_hash_to_challenge.extend(
                expected_final_digest
                    .as_limbs::<CS>()
                    .into_iter()
                    .enumerate()
                    .map(|(i, n)| {
                        n.as_sapling_allocated_num(
                            cs.namespace(|| format!("final digest hash {}", i)),
                        )
                    })
                    .collect::<Result<Vec<_>, _>>()?,
            );
            to_hash_to_challenge.extend(insertions.iter().map(|i| i.hash.clone().unwrap()));
            to_hash_to_challenge.extend(removals.iter().map(|i| i.hash.clone().unwrap()));
            pocklington::hash_to_pocklington_prime(
                cs.namespace(|| "chash"),
                &to_hash_to_challenge,
                limb_width,
                self.params.n_bits_challenge,
                &self.params.hasher,
            )?
        };

        if self.params.verbose {
            println!("Constructing Group");
        }
        let group = {
            let raw_group = self
                .inputs
                .as_ref()
                .map(|s| s.initial_state.group().clone());
            let group = CircuitRsaQuotientGroup::alloc(
                cs.namespace(|| "group"),
                raw_group.as_ref(),
                (),
                &CircuitRsaGroupParams {
                    limb_width,
                    n_limbs: n_bits_base / limb_width,
                },
            )?;
            group.inputize_hash(cs.namespace(|| "group input"), &self.params.hasher)?;
            group
        };

        if self.params.verbose {
            println!("Constructing Sets");
        }

        let initial_set = {
            let initial_set: CircuitSet<E, H, CircuitRsaQuotientGroup<E>, Inner> =
                CircuitSet::alloc(
                    cs.namespace(|| "set init"),
                    self.inputs.as_ref().map(|is| &is.initial_state),
                    (group.clone(), challenge.clone()),
                    &CircuitSetParams {
                        hasher: self.params.hasher.clone(),
                        n_bits: self.params.n_bits_elem,
                        limb_width,
                    },
                )?;
            initial_set
                .inputize_hash(cs.namespace(|| "initial_state input"), &self.params.hasher)?;
            initial_set.inner.digest.equal(
                cs.namespace(|| "initial digest matches"),
                &expected_initial_digest,
            )?;
            initial_set
        };

        let final_set = {
            let final_set: CircuitSet<E, H, CircuitRsaQuotientGroup<E>, Inner> = CircuitSet::alloc(
                cs.namespace(|| "set final"),
                self.inputs.as_ref().map(|is| &is.final_state),
                (group, challenge),
                &CircuitSetParams {
                    hasher: self.params.hasher.clone(),
                    n_bits: self.params.n_bits_elem,
                    limb_width,
                },
            )?;
            final_set.inputize_hash(cs.namespace(|| "final_state input"), &self.params.hasher)?;
            final_set.inner.digest.equal(
                cs.namespace(|| "final digest matches"),
                &expected_final_digest,
            )?;
            final_set
        };

        if self.params.verbose {
            println!("Swapping elements");
        }
        initial_set.verify_swap_all(cs.namespace(|| "swap"), removals, insertions, final_set)?;

        if self.params.verbose {
            println!("Done with synthesis");
        }
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

    use hash::hashes::Poseidon;

    use set::int_set::NaiveExpSet;

    use util::test_helpers::*;

    circuit_tests! {
        small_rsa_1_swap_naive: (SetBench::<_, NaiveExpSet<_>>  {
            inputs: Some(SetBenchInputs::new(
                            [].to_vec(),
                            [
                            ["0", "1", "2", "3", "4"].iter().map(|s| s.to_string()).collect(),
                            ].to_vec(),
                            [
                            ["0", "1", "2", "3", "5"].iter().map(|s| s.to_string()).collect(),
                            ].to_vec(),
                            Poseidon::default(),
                            128,
                            32,
                            RsaQuotientGroup {
                                g: BigUint::from(2usize),
                                m: BigUint::from_str(RSA_512).unwrap(),
                            },
                    )),
                    params: SetBenchParams {
                        group: RsaQuotientGroup {
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
                        hasher: Poseidon::default(),
                        verbose: true,
                    },
        }, true),

        //large_rsa_1_swap_parallel: (SetBench::<_, ParallelExpSet<_>>  {
        //    inputs: Some(SetBenchInputs::new(
        //                    [].to_vec(),
        //                    [
        //                    ["0", "1", "2", "3", "4"].iter().map(|s| s.to_string()).collect(),
        //                    ].to_vec(),
        //                    [
        //                    ["0", "1", "2", "3", "5"].iter().map(|s| s.to_string()).collect(),
        //                    ].to_vec(),
        //                    Poseidon::default(),
        //                    128,
        //                    32,
        //                    RsaQuotientGroup {
        //                        g: BigUint::from(2usize),
        //                        m: BigUint::from_str(RSA_2048).unwrap(),
        //                    },
        //            )),
        //            params: SetBenchParams {
        //                group: RsaQuotientGroup {
        //                    g: BigUint::from(2usize),
        //                    m: BigUint::from_str(RSA_2048).unwrap(),
        //                },
        //                limb_width: 32,
        //                n_bits_elem: 128,
        //                n_bits_challenge: 128,
        //                n_bits_base: 2048,
        //                item_size: 5,
        //                n_inserts: 1,
        //                n_removes: 1,
        //                hasher: Poseidon::default(),
        //                verbose: true,
        //            },
        //}, true),

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
