use num_bigint::BigUint;
use sapling_crypto::bellman::pairing::bn256::Bn256;
use sapling_crypto::bellman::pairing::ff::{PrimeField, ScalarEngine};
use sapling_crypto::bellman::pairing::Engine;
use sapling_crypto::bellman::{Circuit, ConstraintSystem, SynthesisError};
use sapling_crypto::circuit::num::AllocatedNum;
use sapling_crypto::poseidon::bn256::Bn256PoseidonParams;
use sapling_crypto::poseidon::{PoseidonEngine, QuinticSBox};

use bignat::BigNat;
use group::{CircuitRsaGroup, CircuitRsaGroupParams, Gadget, RsaGroup};
use hash::{hash_to_prime, hash_to_rsa_element, helper, HashDomain};
use rsa_set::{CircuitExpSet, ExpSet, NaiveExpSet};
use OptionExt;

pub struct SetInputs<E: Engine, S: ExpSet> {
    /// The initial state of the set
    pub initial_state: S,
    pub final_digest: BigUint,
    /// The items to remove from the set
    pub to_remove: Vec<Vec<E::Fr>>,
    /// The items to insert into the set
    pub to_insert: Vec<Vec<E::Fr>>,
}

impl SetInputs<Bn256, NaiveExpSet<RsaGroup>> {
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
        SetInputs {
            initial_state: set,
            final_digest,
            to_remove: removed,
            to_insert: inserted,
        }
    }
}

#[derive(Clone)]
pub struct SetParams<E: PoseidonEngine> {
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

pub struct Set<E: PoseidonEngine<SBox = QuinticSBox<E>>, S: ExpSet> {
    pub inputs: Option<SetInputs<E, S>>,
    pub params: SetParams<E>,
}

impl<E: PoseidonEngine<SBox = QuinticSBox<E>>> Circuit<E> for Set<E, NaiveExpSet<RsaGroup>> {
    fn synthesize<CS: ConstraintSystem<E>>(self, cs: &mut CS) -> Result<(), SynthesisError> {
        println!("Constructing Group");
        let raw_group = self.inputs.grab()?.initial_state.group().clone();
        let group = CircuitRsaGroup::alloc(
            cs.namespace(|| "group"),
            Some(&raw_group),
            (),
            &CircuitRsaGroupParams {
                limb_width: self.params.limb_width,
                n_limbs: self.params.n_bits_base,
            },
        )?;
        println!("Constructing Set");
        let set: CircuitExpSet<E, RsaGroup, CircuitRsaGroup<E>> = CircuitExpSet::alloc(
            cs.namespace(|| "set init"),
            self.inputs.as_ref().map(|is| &is.initial_state),
            group,
            &(),
        )?;
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
        small_rsa_1_swap: (Set {
            inputs: Some(SetInputs::new(
                [].to_vec(),
                [
                    ["0", "1", "2", "3", "4"].iter().map(|s| s.to_string()).collect(),
                ].to_vec(),
                [
                    ["0", "1", "2", "3", "5"].iter().map(|s| s.to_string()).collect(),
                ].to_vec(),
                &Bn256PoseidonParams::new::<sapling_crypto::group_hash::BlakeHasher>(),
                128,
                RsaGroup {
                    g: BigUint::from(2usize),
                    m: BigUint::from_str(RSA_512).unwrap(),
                },
            )),
            params: SetParams {
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
                hash: Bn256PoseidonParams::new::<sapling_crypto::group_hash::BlakeHasher>(),
            },
        }, true),
        //small_rsa_5_swaps: (Set {
        //    inputs: Some(SetInputs::new(
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
        //    params: SetParams {
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
        //full_rsa_30_swaps: (Set {
        //    inputs: Some(SetInputs::from_counts(
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
        //    params: SetParams {
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
