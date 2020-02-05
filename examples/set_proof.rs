extern crate bellman_bignat;
extern crate docopt;
extern crate num_bigint;
extern crate rand;
extern crate sapling_crypto;
extern crate serde;

use bellman_bignat::group::RsaQuotientGroup;
use bellman_bignat::hash::circuit::CircuitHasher;
use bellman_bignat::hash::hashes::{Mimc, Pedersen, Poseidon, Sha256};
use bellman_bignat::hash::Hasher;
use bellman_bignat::mp::bignat::nat_to_limbs;
use bellman_bignat::set::merkle::{MerkleSetBench, MerkleSetBenchInputs, MerkleSetBenchParams};
use bellman_bignat::set::rsa::{SetBench, SetBenchInputs, SetBenchParams};
use bellman_bignat::set::GenSet;
use docopt::Docopt;
use num_bigint::BigUint;
use sapling_crypto::bellman::groth16::{
    create_random_proof, generate_random_parameters, prepare_verifying_key, verify_proof,
};
use sapling_crypto::bellman::pairing::bls12_381::Bls12;
use sapling_crypto::bellman::pairing::Engine;
use serde::Deserialize;

use std::str::FromStr;
use std::time::Instant;

const USAGE: &str = "
Set Proof Benchmarker

Usage:
  set_proof [options] rsa <transactions> <capacity>
  set_proof [options] merkle <transactions> <capacity>
  set_proof (-h | --help)
  set_proof --version

Options:
  -h --help      Show this screen.
  -f --full      Run the test with an initially full accumulator
  --hash HASH    The hash function to use [default: poseidon]
                 Valid values: poseidon, mimc, pedersen, babypedersen, sha
  --version      Show version.
";

// From https://en.wikipedia.org/wiki/RSA_numbers#RSA-2048
const RSA_2048: &str = "25195908475657893494027183240048398571429282126204032027777137836043662020707595556264018525880784406918290641249515082189298559149176184502808489120072844992687392807287776735971418347270261896375014971824691165077613379859095700097330459748808428401797429100642458691817195118746121515172654632282216869987549182422433637259085141865462043576798423387184774447920739934236584823824281198163815010674810451660377306056201619676256133844143603833904414952634432190114657544454178424020924616515723350778707749817125772467962926386356373289912154831438167899885040445364023527381951378636564391212010397122822120720357";
const RSA_SIZE: usize = 2048;
const ELEMENT_SIZE: usize = 5;

#[derive(Debug, Deserialize)]
enum Hashes {
    Poseidon,
    Mimc,
    Pedersen,
    Sha,
}

#[derive(Debug, Deserialize)]
struct Args {
    arg_transactions: usize,
    arg_capacity: usize,
    flag_hash: Hashes,
    flag_full: bool,
    cmd_rsa: bool,
    cmd_merkle: bool,
}

fn main() {
    color_backtrace::install();
    let args: Args = Docopt::new(USAGE)
        .and_then(|d| d.deserialize())
        .unwrap_or_else(|e| e.exit());

    if args.cmd_merkle {
        match args.flag_hash {
            Hashes::Poseidon => merkle_bench::<Bls12, _>(
                args.arg_transactions,
                args.arg_capacity,
                args.flag_full,
                Poseidon::default(),
            ),
            Hashes::Mimc => merkle_bench::<Bls12, _>(
                args.arg_transactions,
                args.arg_capacity,
                args.flag_full,
                Mimc::default(),
            ),
            Hashes::Pedersen => merkle_bench::<Bls12, _>(
                args.arg_transactions,
                args.arg_capacity,
                args.flag_full,
                Pedersen::default(),
            ),
            Hashes::Sha => merkle_bench::<Bls12, _>(
                args.arg_transactions,
                args.arg_capacity,
                args.flag_full,
                Sha256::default(),
            ),
        }
    } else if args.cmd_rsa {
        match args.flag_hash {
            Hashes::Poseidon => rsa_bench::<Bls12, _>(
                args.arg_transactions,
                args.arg_capacity,
                args.flag_full,
                Poseidon::default(),
            ),
            Hashes::Mimc => rsa_bench::<Bls12, _>(
                args.arg_transactions,
                args.arg_capacity,
                args.flag_full,
                Mimc::default(),
            ),
            Hashes::Pedersen => rsa_bench::<Bls12, _>(
                args.arg_transactions,
                args.arg_capacity,
                args.flag_full,
                Pedersen::default(),
            ),
            Hashes::Sha => rsa_bench::<Bls12, _>(
                args.arg_transactions,
                args.arg_capacity,
                args.flag_full,
                Sha256::default(),
            ),
        }
    }
}

fn rsa_bench<E: Engine, H: Hasher<F = E::Fr> + CircuitHasher<E = E>>(
    t: usize,
    c: usize,
    full: bool,
    hash: H,
) {
    use rand::thread_rng;

    let rng = &mut thread_rng();

    let group = RsaQuotientGroup {
        g: BigUint::from(2usize),
        m: BigUint::from_str(RSA_2048).unwrap(),
    };

    let n_untouched = if full {
        (1usize << c).saturating_sub(t)
    } else {
        0
    };
    let params = SetBenchParams {
        group: group.clone(),
        limb_width: 32,
        n_bits_elem: RSA_SIZE,
        n_bits_challenge: 256,
        n_bits_base: RSA_SIZE,
        item_size: ELEMENT_SIZE,
        n_inserts: t,
        n_removes: t,
        hasher: hash.clone(),
        verbose: true,
    };

    let empty_circuit = SetBench {
        inputs: None,
        params: params.clone(),
    };

    let circuit = SetBench {
        inputs: Some(SetBenchInputs::from_counts(
            n_untouched,
            t,
            t,
            ELEMENT_SIZE,
            hash,
            RSA_SIZE,
            32,
            RsaQuotientGroup {
                g: BigUint::from(2usize),
                m: BigUint::from_str(RSA_2048).unwrap(),
            },
        )),
        params: params.clone(),
    };

    let params = {
        let generate_params_start = Instant::now();
        let p = generate_random_parameters(empty_circuit, rng);
        let generate_params_end = Instant::now();
        println!("Params are okay: {:#?}", p.is_ok());
        println!(
            "Done with parameters, duration {:?}",
            generate_params_end - generate_params_start
        );
        p.unwrap()
    };

    let pvk = prepare_verifying_key(&params.vk);
    println!("Done with key");

    let ins = circuit.inputs.as_ref().unwrap();
    let mut initial_set = ins.initial_state.clone();
    let mut final_set = {
        let mut t = initial_set.clone();
        t.swap_all(ins.to_remove.clone(), ins.to_insert.clone());
        t
    };
    let mut inputs: Vec<E::Fr> = nat_to_limbs(&group.g, 32, 64).unwrap();
    inputs.extend(nat_to_limbs::<E::Fr>(&group.m, 32, 64).unwrap());
    inputs.extend(nat_to_limbs::<E::Fr>(&initial_set.digest(), 32, 64).unwrap());
    inputs.extend(nat_to_limbs::<E::Fr>(&final_set.digest(), 32, 64).unwrap());

    let prover_start = Instant::now();

    let proof = create_random_proof(circuit, &params, rng).unwrap();

    let prover_end = Instant::now();
    println!("Done with proof, duration: {:?}", prover_end - prover_start);

    let verifier_start = Instant::now();

    let result = verify_proof(&pvk, &proof, &inputs);

    let verifier_end = Instant::now();
    println!(
        "Done with verifcation: {:?}, duration: {:?}",
        result,
        verifier_end - verifier_start
    );
}

fn merkle_bench<E: Engine, H: Hasher<F = E::Fr> + CircuitHasher<E = E>>(
    t: usize,
    c: usize,
    full: bool,
    hash: H,
) {
    use rand::thread_rng;

    let rng = &mut thread_rng();

    let merkle_params = MerkleSetBenchParams {
        item_size: ELEMENT_SIZE,
        n_swaps: t,
        hash: hash.clone(),
        depth: c,
        verbose: true,
    };
    let empty_circuit = MerkleSetBench {
        inputs: None,
        params: merkle_params.clone(),
    };

    // Create a groth16 proof with our parameters.
    let merkle_inputs = MerkleSetBenchInputs::from_counts(
        if full { (1 << c) - t } else { 0 },
        t,
        ELEMENT_SIZE,
        hash,
        c,
    );

    let circuit = MerkleSetBench {
        inputs: Some(merkle_inputs),
        params: merkle_params,
    };

    let params = {
        let generate_params_start = Instant::now();
        let p = generate_random_parameters(empty_circuit, rng);
        let generate_params_end = Instant::now();
        println!("Params are okay: {:#?}", p.is_ok());
        println!(
            "Done with parameters, duration {:?}",
            generate_params_end - generate_params_start
        );
        p.unwrap()
    };

    let pvk = prepare_verifying_key(&params.vk);
    println!("Done with key");

    let ins = circuit.inputs.as_ref().unwrap();
    let mut initial_set = ins.initial_state.clone();
    let mut final_set = {
        let mut t = initial_set.clone();
        t.swap_all(ins.to_remove.clone(), ins.to_insert.clone());
        t
    };
    let inputs: Vec<E::Fr> = vec![initial_set.digest(), final_set.digest()];

    let verifier_start = Instant::now();

    let proof = create_random_proof(circuit, &params, rng).unwrap();

    let verifier_end = Instant::now();
    println!(
        "Done with proof, duration: {:?}",
        verifier_end - verifier_start
    );

    let verifier_start = Instant::now();

    let result = verify_proof(&pvk, &proof, &inputs);

    let verifier_end = Instant::now();
    println!(
        "Done with verifcation: {:?}, duration: {:?}",
        result,
        verifier_end - verifier_start
    );
}
