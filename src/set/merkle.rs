use fnv::FnvHashMap;
use sapling_crypto::bellman::pairing::ff::{PrimeField, ScalarEngine};
use sapling_crypto::bellman::pairing::Engine;
use sapling_crypto::bellman::{Circuit, ConstraintSystem, LinearCombination, SynthesisError};
use sapling_crypto::circuit::boolean::{AllocatedBit, Boolean};
use sapling_crypto::circuit::num::AllocatedNum;
use sapling_crypto::poseidon::{PoseidonEngine, QuinticSBox};

use std::collections::BTreeMap;
use std::rc::Rc;

use super::GenSet;
use gadget::Gadget;
use hash::tree::circuit::{CircuitHasher, CircuitPoseidon};
use hash::tree::{Hasher, Poseidon};
use usize_to_f;
use OptionExt;

/// Represents a merkle tree in which some prefix of the capacity is occupied.
/// Unoccupied leaves are assumed to be zero. This allows nodes with no occupied children to have a
/// pre-determined hash.
#[derive(Clone)]
pub struct MerkleSet<E, H>
where
    E: Engine,
    H: Hasher<E::Fr>,
{
    pub hasher: H,

    /// Level i holds 2 ** i elements. Level 0 is the root.
    /// Maps (level, idx in level) -> hash value
    pub nodes: FnvHashMap<(usize, usize), E::Fr>,

    /// default[i] is the hash value for a node at level i which has no occupied descendents
    pub defaults: Vec<E::Fr>,

    /// The number of non-root levels. The number of leaves is 2 ** depth.
    pub depth: usize,

    /// Map from a leave to its index in the array of leaves
    pub leaf_indices: BTreeMap<<E::Fr as PrimeField>::Repr, usize>,
}

impl<E, H> MerkleSet<E, H>
where
    E: Engine,
    H: Hasher<E::Fr>,
{
    pub fn new_with<'b>(
        hasher: H,
        depth: usize,
        items: impl IntoIterator<Item = &'b [E::Fr]>,
    ) -> Self {
        let leaves: Vec<E::Fr> = items.into_iter().map(|s| hasher.hash(s)).collect();
        let n = leaves.len();
        let leaf_indices: BTreeMap<<E::Fr as PrimeField>::Repr, usize> = leaves
            .iter()
            .enumerate()
            .map(|(i, e)| (e.into_repr(), i))
            .collect();

        let mut nodes = FnvHashMap::default();
        for (i, hash) in leaves.into_iter().enumerate() {
            nodes.insert((depth, i), hash);
        }
        let defaults = {
            let mut d = vec![usize_to_f::<E::Fr>(0)];
            while d.len() <= depth {
                let prev = d.last().unwrap().clone();
                d.push(hasher.hash(&[prev.clone(), prev]));
            }
            d.reverse();
            d
        };
        let mut this = Self {
            hasher,
            nodes,
            defaults,
            depth,
            leaf_indices,
        };
        for i in 0..n {
            this.update_hashes_from_leaf_index(i);
        }
        this
    }
}
impl<E, H> MerkleSet<E, H>
where
    E: Engine,
    H: Hasher<E::Fr>,
{
    fn get_node(&self, level: usize, index: usize) -> &E::Fr {
        self.nodes
            .get(&(level, index))
            .unwrap_or_else(|| &self.defaults[level])
    }

    fn hash(&self, child_1: &E::Fr, child_2: &E::Fr) -> E::Fr {
        self.hasher.hash(&[child_1.clone(), child_2.clone()])
    }

    fn update_hashes_from_leaf_index(&mut self, mut index: usize) {
        index /= 2;
        for level in (0..self.depth).rev() {
            let child_1 = self.get_node(level + 1, 2 * index);
            let child_2 = self.get_node(level + 1, 2 * index + 1);
            let hash = self.hash(child_1, child_2);
            self.nodes.insert((level, index), hash);
            index /= 2;
        }
    }

    /// Given an item, returns the witness that the item is in the set. The witness is a sequence
    /// of pairs (bit, hash), where bit is true if hash is a right child on the path to the item.
    /// The sequence starts at the top of the tree, going down.
    fn witness(&self, item: &[E::Fr]) -> Vec<(bool, E::Fr)> {
        println!("{:?}", self.leaf_indices);
        let o_r = self.hasher.hash(item).into_repr();
        let i = *self
            .leaf_indices
            .get(&o_r)
            .expect("missing element in MerkleSet::witness");
        (0..self.depth)
            .map(|level| {
                let index_at_level = i >> (self.depth - (level + 1));
                let bit = index_at_level & 1 == 0;
                let hash = self.get_node(level + 1, index_at_level ^ 1).clone();
                (bit, hash)
            })
            .collect()
    }
}

impl<E, H> GenSet<E> for MerkleSet<E, H>
where
    E: Engine,
    H: Hasher<E::Fr>,
{
    type Digest = E::Fr;

    fn swap(&mut self, old: &[E::Fr], new: Vec<E::Fr>) {
        let o_r = self.hasher.hash(old).into_repr();
        let n = self.hasher.hash(&new);
        let n_r = n.into_repr();
        let i = *self
            .leaf_indices
            .get(&o_r)
            .expect("missing element in MerkleSet::swap");
        self.nodes.insert((self.depth, i), n);
        self.leaf_indices.remove(&o_r);
        self.leaf_indices.insert(n_r, i);
        self.update_hashes_from_leaf_index(i);
    }

    /// The digest of the current elements (`g` to the product of the elements).
    fn digest(&self) -> Self::Digest {
        self.get_node(0, 0).clone()
    }
}

pub struct MerkleCircuitSetParams<HParams> {
    hash: Rc<HParams>,
    depth: usize,
}

impl<HParams> std::clone::Clone for MerkleCircuitSetParams<HParams> {
    fn clone(&self) -> Self {
        Self {
            hash: self.hash.clone(),
            depth: self.depth,
        }
    }
}

pub struct MerkleCircuitSet<E, H, CH>
where
    E: Engine,
    H: Hasher<E::Fr>,
    CH: CircuitHasher<E>,
{
    pub value: Option<MerkleSet<E, H>>,
    pub digest: AllocatedNum<E>,
    pub depth: usize,
    pub hasher: CH,
}

impl<E, H, CH> std::clone::Clone for MerkleCircuitSet<E, H, CH>
where
    E: Engine,
    H: Hasher<E::Fr>,
    CH: CircuitHasher<E>,
{
    fn clone(&self) -> Self {
        Self {
            value: self.value.clone(),
            depth: self.depth,
            hasher: self.hasher.clone(),
            digest: self.digest.clone(),
        }
    }
}

impl<E, H, CH> Gadget for MerkleCircuitSet<E, H, CH>
where
    E: Engine,
    H: Hasher<E::Fr>,
    CH: CircuitHasher<E>,
{
    type E = E;
    type Value = MerkleSet<E, H>;
    type Access = CH;
    type Params = usize;
    fn alloc<CS: ConstraintSystem<Self::E>>(
        mut cs: CS,
        value: Option<&Self::Value>,
        access: Self::Access,
        params: &Self::Params,
    ) -> Result<Self, SynthesisError> {
        let digest = AllocatedNum::alloc(cs.namespace(|| "digest"), || Ok(value.grab()?.digest()))?;
        Ok(Self {
            value: value.cloned(),
            hasher: access,
            depth: *params,
            digest,
        })
    }
    fn wires(&self) -> Vec<LinearCombination<Self::E>> {
        vec![LinearCombination::zero() + self.digest.get_variable()]
    }
    fn wire_values(&self) -> Option<Vec<<Self::E as ScalarEngine>::Fr>> {
        self.digest.get_value().map(|d| vec![d])
    }
    fn value(&self) -> Option<&Self::Value> {
        self.value.as_ref()
    }
    fn access(&self) -> &Self::Access {
        &self.hasher
    }
    fn params(&self) -> &Self::Params {
        &self.depth
    }
}

impl<E, H, CH> MerkleCircuitSet<E, H, CH>
where
    E: Engine,
    H: Hasher<E::Fr>,
    CH: CircuitHasher<E>,
{
    pub fn swap_all<'b, CS: ConstraintSystem<E>>(
        mut self,
        mut cs: CS,
        removed_items: impl IntoIterator<Item = &'b [AllocatedNum<E>]> + Clone,
        inserted_items: impl IntoIterator<Item = &'b [AllocatedNum<E>]> + Clone,
    ) -> Result<Self, SynthesisError> {
        for (j, (old, new)) in removed_items
            .into_iter()
            .zip(inserted_items.into_iter())
            .enumerate()
        {
            let mut cs = cs.namespace(|| format!("swap {}", j));

            // First, we allocate the path
            let witness = self.value.as_ref().and_then(|v| {
                old.into_iter()
                    .map(|n| n.get_value())
                    .collect::<Option<Vec<E::Fr>>>()
                    .map(|x| v.witness(&x))
            });
            let path: Vec<(Boolean, AllocatedNum<E>)> = {
                let mut cs = cs.namespace(|| "alloc path");
                (0..self.depth)
                    .map(|i| {
                        let mut cs = cs.namespace(|| format!("{}", i));
                        Ok((
                            Boolean::from(AllocatedBit::alloc(
                                cs.namespace(|| "direction"),
                                witness.as_ref().map(|w| w[i].0),
                            )?),
                            AllocatedNum::alloc(cs.namespace(|| "hash"), || {
                                Ok(witness.grab()?[i].1)
                            })?,
                        ))
                    })
                    .collect::<Result<Vec<(Boolean, AllocatedNum<E>)>, SynthesisError>>()?
            };

            // Now, check the old item
            {
                let mut cs = cs.namespace(|| "check old");
                let mut acc = self.hasher.hash(cs.namespace(|| "leaf hash"), old)?;
                for (i, (bit, hash)) in path.iter().enumerate().rev() {
                    let mut cs = cs.namespace(|| format!("level {}", i));
                    let (a, b) = AllocatedNum::conditionally_reverse(
                        cs.namespace(|| "order"),
                        &hash,
                        &acc,
                        &bit,
                    )?;
                    acc = self.hasher.hash(cs.namespace(|| "hash"), &[a, b])?;
                }
                let eq = AllocatedNum::equals(cs.namespace(|| "root check"), &acc, &self.digest)?;
                Boolean::enforce_equal(
                    cs.namespace(|| "root check passes"),
                    &eq,
                    &Boolean::constant(true),
                )?;
            }

            // Now, add the new item
            {
                let mut cs = cs.namespace(|| "add new");
                let mut acc = self.hasher.hash(cs.namespace(|| "leaf hash"), new)?;
                for (i, (bit, hash)) in path.into_iter().enumerate().rev() {
                    let mut cs = cs.namespace(|| format!("level {}", i));
                    let (a, b) = AllocatedNum::conditionally_reverse(
                        cs.namespace(|| "order"),
                        &hash,
                        &acc,
                        &bit,
                    )?;
                    acc = self.hasher.hash(cs.namespace(|| "hash"), &[a, b])?;
                }
                self.digest = acc;
                if let Some(v) = self.value.as_mut() {
                    let o = old
                        .into_iter()
                        .map(|n| n.get_value())
                        .collect::<Option<Vec<E::Fr>>>();
                    let n = new
                        .into_iter()
                        .map(|n| n.get_value())
                        .collect::<Option<Vec<E::Fr>>>();
                    if let (Some(o), Some(n)) = (o, n) {
                        v.swap(&o, n);
                    }
                }
            }
        }
        Ok(self)
    }
}

pub struct MerkleSetBenchInputs<E>
where
    E: PoseidonEngine<SBox = QuinticSBox<E>>,
{
    /// The initial state of the set
    pub initial_state: MerkleSet<E, Poseidon<E>>,
    /// The items to remove from the set
    pub to_remove: Vec<Vec<E::Fr>>,
    /// The items to insert into the set
    pub to_insert: Vec<Vec<E::Fr>>,
}

impl<E> MerkleSetBenchInputs<E>
where
    E: PoseidonEngine<SBox = QuinticSBox<E>>,
{
    pub fn from_counts(
        n_untouched: usize,
        n_swaps: usize,
        item_len: usize,
        hash: Rc<E::Params>,
        depth: usize,
    ) -> Self {
        assert!(n_untouched < (1 << depth));
        let items: Vec<Vec<String>> = (0..(n_untouched + 2 * n_swaps))
            .map(|i| {
                (0..item_len)
                    .map(|j| format!("1{:06}{:03}", i, j))
                    .collect()
            })
            .collect();
        let initial_items = items[..=n_untouched].to_owned();
        let removed_items = items[n_untouched..(n_untouched + n_swaps)].to_owned();
        let inserted_items = items[(n_untouched + 1)..(n_untouched + n_swaps + 1)].to_owned();

        Self::new(initial_items, removed_items, inserted_items, hash, depth)
    }
    pub fn new(
        initial_items: Vec<Vec<String>>,
        removed_items: Vec<Vec<String>>,
        inserted_items: Vec<Vec<String>>,
        hash: Rc<E::Params>,
        depth: usize,
    ) -> Self {
        let initial: Vec<Vec<E::Fr>> = initial_items
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
        assert!((1 << depth) >= initial.len());
        assert_eq!(removed.len(), inserted.len());
        let hasher = Poseidon {
            params: hash,
        };
        let initial_state = MerkleSet::new_with(hasher, depth, initial.iter().map(Vec::as_slice));
        Self {
            initial_state,
            to_remove: removed,
            to_insert: inserted,
        }
    }
}

#[derive(Clone)]
pub struct MerkleSetBenchParams<E: PoseidonEngine> {
    pub item_size: usize,
    pub n_swaps: usize,
    pub hash: Rc<E::Params>,
    pub depth: usize,
    pub verbose: bool,
}

pub struct MerkleSetBench<E>
where
    E: PoseidonEngine<SBox = QuinticSBox<E>>,
{
    pub inputs: Option<MerkleSetBenchInputs<E>>,
    pub params: MerkleSetBenchParams<E>,
}

impl<E> Circuit<E> for MerkleSetBench<E>
where
    E: PoseidonEngine<SBox = QuinticSBox<E>>,
{
    fn synthesize<CS: ConstraintSystem<E>>(self, cs: &mut CS) -> Result<(), SynthesisError> {
        if self.params.verbose {
            println!("Constructing Set");
        }
        let hasher = CircuitPoseidon::<E> {
            params: self.params.hash.clone(),
        };
        let set = MerkleCircuitSet::alloc(
            cs.namespace(|| "set init"),
            self.inputs.as_ref().map(|is| &is.initial_state),
            hasher,
            &self.params.depth,
        )?;
        set.inputize(cs.namespace(|| "initial_state input"))?;
        if self.params.verbose {
            println!("Allocating Deletions...");
        }
        let removals = (0..self.params.n_swaps)
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
        let insertions = (0..self.params.n_swaps)
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

        if self.params.verbose {
            println!("Swapping elements");
        }
        let new_set = set.swap_all(
            cs.namespace(|| "swap"),
            removals.iter().map(Vec::as_slice),
            insertions.iter().map(Vec::as_slice),
        )?;

        if self.params.verbose {
            println!("NOT Verifying resulting digest");
        }
        new_set.inputize(cs.namespace(|| "final_state input"))?;
        Ok(())
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use sapling_crypto::group_hash::Keccak256Hasher;
    use sapling_crypto::poseidon::bn256::Bn256PoseidonParams;
    use test_helpers::*;
    circuit_tests! {
        merkle_1_swap_3_depth: (MerkleSetBench {
            inputs: Some(MerkleSetBenchInputs::from_counts(
                            0,
                            1,
                            5,
                            Rc::new(Bn256PoseidonParams::new::<Keccak256Hasher>()),
                            3
                    )),
                    params: MerkleSetBenchParams {
                        item_size: 5,
                        n_swaps: 1,
                        hash: Rc::new(Bn256PoseidonParams::new::<Keccak256Hasher>()),
                        verbose: true,
                        depth: 3,
                    },
        }, true),
        merkle_1_swap_10_depth: (MerkleSetBench {
            inputs: Some(MerkleSetBenchInputs::from_counts(
                            0,
                            1,
                            5,
                            Rc::new(Bn256PoseidonParams::new::<Keccak256Hasher>()),
                            10
                    )),
                    params: MerkleSetBenchParams {
                        item_size: 5,
                        n_swaps: 1,
                        hash: Rc::new(Bn256PoseidonParams::new::<Keccak256Hasher>()),
                        verbose: true,
                        depth: 10,
                    },
        }, true),
        merkle_1_swap_25_depth: (MerkleSetBench {
            inputs: Some(MerkleSetBenchInputs::from_counts(
                            0,
                            1,
                            5,
                            Rc::new(Bn256PoseidonParams::new::<Keccak256Hasher>()),
                            25
                    )),
                    params: MerkleSetBenchParams {
                        item_size: 5,
                        n_swaps: 1,
                        hash: Rc::new(Bn256PoseidonParams::new::<Keccak256Hasher>()),
                        verbose: true,
                        depth: 25,
                    },
        }, true),
        merkle_3_swap_25_depth: (MerkleSetBench {
            inputs: Some(MerkleSetBenchInputs::from_counts(
                            0,
                            3,
                            5,
                            Rc::new(Bn256PoseidonParams::new::<Keccak256Hasher>()),
                            25
                    )),
                    params: MerkleSetBenchParams {
                        item_size: 5,
                        n_swaps: 3,
                        hash: Rc::new(Bn256PoseidonParams::new::<Keccak256Hasher>()),
                        verbose: true,
                        depth: 25,
                    },
        }, true),
    }
}
