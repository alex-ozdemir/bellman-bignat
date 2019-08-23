extern crate bellman_bignat;
extern crate num_bigint;
extern crate rand;
extern crate sapling_crypto;

use bellman_bignat::bignat::BigNat;
use bellman_bignat::hash::hash_to_rsa_element;
use bellman_bignat::hash::helper;
use bellman_bignat::rsa_set::{
    AllocatedRsaGroup, NaiveRsaSetBackend, RsaGroup, RsaGroupParams, RsaSet, RsaSetBackend,
};
use num_bigint::BigUint;
use sapling_crypto::bellman::pairing::bn256::Bn256;
use sapling_crypto::bellman::pairing::ff::{PrimeField, ScalarEngine};
use sapling_crypto::bellman::pairing::Engine;
use sapling_crypto::bellman::{Circuit, ConstraintSystem, SynthesisError};
use sapling_crypto::circuit::num::AllocatedNum;
use sapling_crypto::poseidon::bn256::Bn256PoseidonParams;
use sapling_crypto::poseidon::{PoseidonEngine, QuinticSBox};

use std::str::FromStr;

const LIMB_WIDTH: usize = 32;
const N_LIMBS_BASE: usize = 64;
const N_LIMBS_CHALLENGE: usize = 4;
const N_LIMBS_ELEM: usize = 32;
// From https://en.wikipedia.org/wiki/RSA_numbers#RSA-2048
const RSA_2048: &str = "25195908475657893494027183240048398571429282126204032027777137836043662020707595556264018525880784406918290641249515082189298559149176184502808489120072844992687392807287776735971418347270261896375014971824691165077613379859095700097330459748808428401797429100642458691817195118746121515172654632282216869987549182422433637259085141865462043576798423387184774447920739934236584823824281198163815010674810451660377306056201619676256133844143603833904414952634432190114657544454178424020924616515723350778707749817125772467962926386356373289912154831438167899885040445364023527381951378636564391212010397122822120720357";

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

struct RollupInputs<E: Engine, S: RsaSetBackend> {
    /// The initial state of the set
    initial_state: S,
    /// The items to remove from the set
    to_remove: Vec<Vec<E::Fr>>,
    /// The items to insert into the set
    to_insert: Vec<Vec<E::Fr>>,
}

impl RollupInputs<Bn256, NaiveRsaSetBackend> {
    fn new(
        untouched_items: &[&[&str]],
        removed_items: &[&[&str]],
        inserted_items: &[&[&str]],
        hash: &Bn256PoseidonParams,
    ) -> Self {
        let group = RsaGroup {
            g: BigUint::from(2usize),
            m: BigUint::from_str(RSA_2048).unwrap(),
        };
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
            .map(|xs| helper::hash_to_rsa_element::<Bn256>(&xs, hash));
        let removed_hashes = removed
            .iter()
            .map(|xs| helper::hash_to_rsa_element::<Bn256>(&xs, hash));
        let set = NaiveRsaSetBackend::new_with(group, untouched_hashes.chain(removed_hashes));
        RollupInputs {
            initial_state: set,
            to_remove: removed,
            to_insert: inserted,
        }
    }
}

#[derive(Clone)]
struct RollupParams<E: PoseidonEngine> {
    item_size: usize,
    n_removes: usize,
    n_inserts: usize,
    hash: E::Params,
}

struct Rollup<E: PoseidonEngine<SBox = QuinticSBox<E>>, S: RsaSetBackend> {
    inputs: Option<RollupInputs<E, S>>,
    params: RollupParams<E>,
}

impl<E: PoseidonEngine<SBox = QuinticSBox<E>>, S: RsaSetBackend> Circuit<E> for Rollup<E, S> {
    fn synthesize<CS: ConstraintSystem<E>>(mut self, cs: &mut CS) -> Result<(), SynthesisError> {
        let raw_group = RsaGroup {
            g: BigUint::from(2usize),
            m: BigUint::from_str(RSA_2048).unwrap(),
        };
        let group = AllocatedRsaGroup::alloc(
            cs.namespace(|| "group"),
            || Ok(raw_group.g.clone()),
            || Ok(raw_group.m.clone()),
            RsaGroupParams {
                limb_width: LIMB_WIDTH,
                n_limbs: N_LIMBS_BASE,
            },
        )?;
        let challenge = BigNat::alloc_from_nat(
            cs.namespace(|| "challenge"),
            || Ok(BigUint::from_str(CHALLENGE).unwrap()),
            LIMB_WIDTH,
            N_LIMBS_CHALLENGE,
        )?;
        let set = RsaSet::alloc(
            cs.namespace(|| "set init"),
            || {
                Ok({
                    let backend = std::mem::replace(
                        &mut self.inputs.grab_mut()?.initial_state,
                        S::new(raw_group),
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
                    &self.params.hash,
                )
            })
            .collect::<Result<Vec<BigNat<E>>, SynthesisError>>()?;
        println!("Insertions constructed");
        let reduced_set = set.remove(cs.namespace(|| "remove"), &challenge, &removals)?;
        println!("Reduction done");
        reduced_set.insert(cs.namespace(|| "remove"), &challenge, &insertions)?;
        println!("Expansion done");
        Ok(())
    }
}

fn main() {
    color_backtrace::install();

    let hash = Bn256PoseidonParams::new::<sapling_crypto::group_hash::Keccak256Hasher>();
    let circuit = Rollup {
        inputs: Some(RollupInputs::new(
            &[],
            &[&["0", "1", "2", "3", "4"]],
            &[&["0", "1", "2", "3", "5"]],
            &hash,
        )),
        params: RollupParams {
            item_size: 5,
            n_inserts: 1,
            n_removes: 1,
            hash,
        },
    };

    use rand::thread_rng;

    use sapling_crypto::bellman::groth16::{
        create_random_proof, generate_random_parameters, prepare_verifying_key, verify_proof,
    };

    let rng = &mut thread_rng();

    let params = {
        let hash = Bn256PoseidonParams::new::<sapling_crypto::group_hash::Keccak256Hasher>();
        let c = Rollup::<_, NaiveRsaSetBackend> {
            inputs: None,
            params: RollupParams {
                item_size: 5,
                n_inserts: 1,
                n_removes: 1,
                hash,
            },
        };
        generate_random_parameters(c, rng).unwrap()
    };
    println!("Done with parameters");

    let pvk = prepare_verifying_key(&params.vk);
    println!("Done with key");

    // Create a groth16 proof with our parameters.
    let proof = create_random_proof(circuit, &params, rng).unwrap();
    println!("Done with proof");

    println!("verified {:?}", verify_proof(&pvk, &proof, &[]));
}
