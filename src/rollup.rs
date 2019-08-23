
use num_bigint::BigUint;
use sapling_crypto::bellman::pairing::bn256::Bn256;
use sapling_crypto::bellman::pairing::ff::{PrimeField, ScalarEngine};
use sapling_crypto::bellman::pairing::Engine;
use sapling_crypto::bellman::{Circuit, ConstraintSystem, SynthesisError};
use sapling_crypto::circuit::num::AllocatedNum;
use sapling_crypto::poseidon::bn256::Bn256PoseidonParams;
use sapling_crypto::poseidon::{PoseidonEngine, QuinticSBox};

use std::str::FromStr;

use bignat::BigNat;
use hash::hash_to_rsa_element;
use hash::helper;
use rsa_set::{
    AllocatedRsaGroup, NaiveRsaSetBackend, RsaGroup, RsaGroupParams, RsaSet, RsaSetBackend,
};

// From https://en.wikipedia.org/wiki/RSA_numbers#RSA-
const RSA_2048: &str = "25195908475657893494027183240048398571429282126204032027777137836043662020707595556264018525880784406918290641249515082189298559149176184502808489120072844992687392807287776735971418347270261896375014971824691165077613379859095700097330459748808428401797429100642458691817195118746121515172654632282216869987549182422433637259085141865462043576798423387184774447920739934236584823824281198163815010674810451660377306056201619676256133844143603833904414952634432190114657544454178424020924616515723350778707749817125772467962926386356373289912154831438167899885040445364023527381951378636564391212010397122822120720357";
// From my machine (openssl)
const RSA_512: &str = "11834783464130424096695514462778870280264989938857328737807205623069291535525952722847913694296392927890261736769191982212777933726583565708193466779811767";

const CHALLENGE: &str = "274481455456098291870407972073878126369";

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

pub struct RollupInputs<E: Engine, S: RsaSetBackend> {
    /// The initial state of the set
    pub initial_state: S,
    /// The items to remove from the set
    pub to_remove: Vec<Vec<E::Fr>>,
    /// The items to insert into the set
    pub to_insert: Vec<Vec<E::Fr>>,
}

impl RollupInputs<Bn256, NaiveRsaSetBackend> {
    pub fn new(
        untouched_items: &[&[&str]],
        removed_items: &[&[&str]],
        inserted_items: &[&[&str]],
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
        let untouched_hashes = untouched
            .iter()
            .map(|xs| helper::hash_to_rsa_element::<Bn256>(&xs, n_bits_elem, hash));
        let removed_hashes = removed
            .iter()
            .map(|xs| helper::hash_to_rsa_element::<Bn256>(&xs, n_bits_elem, hash));
        let set = NaiveRsaSetBackend::new_with(group, untouched_hashes.chain(removed_hashes));
        RollupInputs {
            initial_state: set,
            to_remove: removed,
            to_insert: inserted,
        }
    }
}

#[derive(Clone)]
pub struct RollupParams<E: PoseidonEngine> {
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

pub struct Rollup<E: PoseidonEngine<SBox = QuinticSBox<E>>, S: RsaSetBackend> {
    pub inputs: Option<RollupInputs<E, S>>,
    pub params: RollupParams<E>,
}

impl<E: PoseidonEngine<SBox = QuinticSBox<E>>, S: RsaSetBackend> Circuit<E> for Rollup<E, S> {
    fn synthesize<CS: ConstraintSystem<E>>(mut self, cs: &mut CS) -> Result<(), SynthesisError> {
        let group = AllocatedRsaGroup::alloc(
            cs.namespace(|| "group"),
            || Ok(self.params.group.g.clone()),
            || Ok(self.params.group.m.clone()),
            RsaGroupParams {
                limb_width: self.params.limb_width,
                n_limbs: self.params.n_bits_base / self.params.limb_width,
            },
        )?;
        let challenge = BigNat::alloc_from_nat(
            cs.namespace(|| "challenge"),
            || Ok(BigUint::from_str(CHALLENGE).unwrap()),
            self.params.limb_width,
            self.params.n_bits_challenge / self.params.limb_width,
        )?;
        let set = RsaSet::alloc(
            cs.namespace(|| "set init"),
            || {
                Ok({
                    let backend = std::mem::replace(
                        &mut self.inputs.grab_mut()?.initial_state,
                        S::new(self.params.group.clone()),
                    );
                    backend
                })
            },
            group,
        )?;

        println!("Set constructed");
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
                    self.params.n_bits_elem,
                    &self.params.hash,
                )
            })
            .collect::<Result<Vec<BigNat<E>>, SynthesisError>>()?;
        println!("Deletions constructed");
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
                    self.params.n_bits_elem,
                    &self.params.hash,
                )
            })
            .collect::<Result<Vec<BigNat<E>>, SynthesisError>>()?;
        println!("Insertions constructed");
        let reduced_set = set.remove(cs.namespace(|| "remove"), &challenge, &removals)?;
        println!("Reduction done");
        reduced_set.insert(cs.namespace(|| "insert"), &challenge, &insertions)?;
        println!("Expansion done");
        Ok(())
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use test_helpers::*;

    circuit_tests! {
        small_rsa_1_swap: (Rollup {
            inputs: Some(RollupInputs::new(
                &[],
                &[&["0", "1", "2", "3", "4"]],
                &[&["0", "1", "2", "3", "5"]],
                &Bn256PoseidonParams::new::<sapling_crypto::group_hash::Keccak256Hasher>(),
                128,
                RsaGroup {
                    g: BigUint::from(2usize),
                    m: BigUint::from_str(RSA_512).unwrap(),
                },
            )),
            params: RollupParams {
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
        small_rsa_5_swaps: (Rollup {
            inputs: Some(RollupInputs::new(
                &[],
                &[
                    &["0", "1", "2", "3", "4"],
                    &["1", "1", "2", "3", "4"],
                    &["2", "1", "2", "3", "4"],
                    &["3", "1", "2", "3", "4"],
                    &["4", "1", "2", "3", "4"],
                ],
                &[
                    &["0", "1", "2", "3", "5"],
                    &["0", "1", "2", "3", "6"],
                    &["0", "1", "2", "3", "7"],
                    &["0", "1", "2", "3", "8"],
                    &["0", "1", "2", "3", "9"],
                ],
                &Bn256PoseidonParams::new::<sapling_crypto::group_hash::Keccak256Hasher>(),
                128,
                RsaGroup {
                    g: BigUint::from(2usize),
                    m: BigUint::from_str(RSA_512).unwrap(),
                },
            )),
            params: RollupParams {
                group: RsaGroup {
                    g: BigUint::from(2usize),
                    m: BigUint::from_str(RSA_512).unwrap(),
                },
                limb_width: 32,
                n_bits_elem: 128,
                n_bits_challenge: 128,
                n_bits_base: 512,
                item_size: 5,
                n_inserts: 5,
                n_removes: 5,
                hash: Bn256PoseidonParams::new::<sapling_crypto::group_hash::Keccak256Hasher>(),
            },
        }, true),
        full_rsa_1_swap: (Rollup {
            inputs: Some(RollupInputs::new(
                &[],
                &[&["0", "1", "2", "3", "4"]],
                &[&["0", "1", "2", "3", "5"]],
                &Bn256PoseidonParams::new::<sapling_crypto::group_hash::Keccak256Hasher>(),
                2048,
                RsaGroup {
                    g: BigUint::from(2usize),
                    m: BigUint::from_str(RSA_2048).unwrap(),
                },
            )),
            params: RollupParams {
                group: RsaGroup {
                    g: BigUint::from(2usize),
                    m: BigUint::from_str(RSA_2048).unwrap(),
                },
                limb_width: 32,
                n_bits_elem: 2048,
                n_bits_challenge: 128,
                n_bits_base: 2048,
                item_size: 5,
                n_inserts: 1,
                n_removes: 1,
                hash: Bn256PoseidonParams::new::<sapling_crypto::group_hash::Keccak256Hasher>(),
            },
        }, true),
    }
}
