extern crate bellman_bignat;
extern crate docopt;
extern crate rand;
extern crate sapling_crypto;
extern crate serde;

use bellman_bignat::group::RsaQuotientGroup;
use bellman_bignat::hash::circuit::CircuitHasher;
use bellman_bignat::hash::hashes::{Mimc, Pedersen, Poseidon, Sha256};
use bellman_bignat::hash::Hasher;
use bellman_bignat::mp::bignat::nat_to_limbs;
use bellman_bignat::set::int_set::ExpSet;
use bellman_bignat::set::int_set::exp::parallel::ParExpComb;
use bellman_bignat::set::merkle::{MerkleSetBench, MerkleSetBenchInputs, MerkleSetBenchParams};
use bellman_bignat::set::rsa::{SetBench, SetBenchInputs, SetBenchParams};
use bellman_bignat::set::GenSet;
use bellman_bignat::util::verbose;
use docopt::Docopt;
use sapling_crypto::bellman::groth16::{
    generate_random_parameters, prepare_prover, prepare_verifying_key, verify_proof,
    ParameterSource, Parameters, Proof,
};
use sapling_crypto::bellman::pairing::bls12_381::Bls12;
use sapling_crypto::bellman::pairing::Engine;
use sapling_crypto::bellman::{Circuit, SynthesisError};
use serde::Deserialize;

use rand::{thread_rng, Rng};
use std::time::{Duration, Instant};

const USAGE: &str = "
Set Proof Benchmarker

Usage:
  set_proof [options] rsa <transactions> <capacity>
  set_proof [options] merkle <transactions> <capacity>
  set_proof (-h | --help)
  set_proof --version

Options:
  -h --help       Show this screen.
  -f --full       Run the test with an initially full accumulator
  -v --verbose    Emit debug statements.
  --oparams FILE  Dump parameters to FILE and exit
  --iparams FILE  Read parameters from FILE
  --hash HASH     The hash function to use [default: poseidon]
                  Valid values: poseidon, mimc, pedersen, babypedersen, sha
  --version       Show version.
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
    flag_verbose: bool,
    flag_oparams: Option<String>,
    flag_iparams: Option<String>,
    cmd_rsa: bool,
    cmd_merkle: bool,
}

#[derive(Debug)]
struct TimeReport {
    init: Duration,
    param_gen: Duration,
    prover_synth: Duration,
    prover_crypto: Duration,
    verifier: Duration,
}

fn main() {
    color_backtrace::install();
    let args: Args = Docopt::new(USAGE)
        .and_then(|d| d.deserialize())
        .unwrap_or_else(|e| e.exit());
    if args.flag_verbose {
        verbose::set_verbose_mode(true);
    }

    let (set, report) = if args.cmd_merkle {
        (
            "merkle",
            match args.flag_hash {
                Hashes::Poseidon => merkle_bench::<Bls12, _>(&args, Poseidon::default()),
                Hashes::Mimc => merkle_bench::<Bls12, _>(&args, Mimc::default()),
                Hashes::Pedersen => merkle_bench::<Bls12, _>(&args, Pedersen::default()),
                Hashes::Sha => merkle_bench::<Bls12, _>(&args, Sha256::default()),
            },
        )
    } else if args.cmd_rsa {
        (
            "rsa",
            match args.flag_hash {
                Hashes::Poseidon => rsa_bench::<Bls12, _>(&args, Poseidon::default()),
                Hashes::Mimc => rsa_bench::<Bls12, _>(&args, Mimc::default()),
                Hashes::Pedersen => rsa_bench::<Bls12, _>(&args, Pedersen::default()),
                Hashes::Sha => rsa_bench::<Bls12, _>(&args, Sha256::default()),
            },
        )
    } else {
        unreachable!()
    };
    println!(
        "{},{},{},{},{},{},{},{}",
        set,
        args.arg_transactions,
        args.arg_capacity,
        report.init.as_secs_f64(),
        report.param_gen.as_secs_f64(),
        report.prover_synth.as_secs_f64(),
        report.prover_crypto.as_secs_f64(),
        report.verifier.as_secs_f64(),
    );
}

/// A copy of the `create_random_proof` procedure of bellman.
/// Returns the proof, the time spent synthesizing the circuit and its inputs, and the time spent
/// doing cryptography.
fn create_random_proof<E, C, R, P: ParameterSource<E>>(
    circuit: C,
    params: P,
    rng: &mut R,
) -> Result<(Proof<E>, Duration, Duration), SynthesisError>
where
    E: Engine,
    C: Circuit<E>,
    R: Rng,
{
    let synth_start = Instant::now();
    let r = rng.gen();
    let s = rng.gen();
    let prover = prepare_prover(circuit)?;
    let synth_end = Instant::now();

    let crypto_start = Instant::now();
    let proof = prover.create_proof(params, r, s)?;
    let crypto_end = Instant::now();

    Ok((proof, synth_end - synth_start, crypto_end - crypto_start))
}

fn rsa_bench<E: Engine, H: Hasher<F = E::Fr> + CircuitHasher<E = E>>(
    args: &Args,
    hash: H,
) -> TimeReport {
    let rng = &mut thread_rng();

    if args.flag_verbose {
        println!("Initializing accumulators, circuits");
    }
    let init_start = Instant::now();
    let group = RsaQuotientGroup::from_strs("2", RSA_2048);

    let n_untouched = if args.flag_full {
        (1usize << args.arg_capacity).saturating_sub(args.arg_transactions)
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
        n_inserts: args.arg_transactions,
        n_removes: args.arg_transactions,
        hasher: hash.clone(),
        verbose: args.flag_verbose,
    };

    let empty_circuit = SetBench::<_, ExpSet<_, ParExpComb>> {
        inputs: None,
        params: params.clone(),
    };
    if args.flag_verbose {
        println!("  Constructing initial and final states");
    }
    let inputs = SetBenchInputs::from_counts(
        n_untouched,
        args.arg_transactions,
        args.arg_transactions,
        ELEMENT_SIZE,
        hash.clone(),
        RSA_SIZE,
        32,
        group.clone(),
    );

    let mut circuit = SetBench::<_, ExpSet<_, ParExpComb>> {
        inputs: Some(inputs),
        params: params.clone(),
    };
    let inputs = circuit.inputs.as_mut().unwrap();
    if args.flag_verbose {
        println!("Marshalling circuit inputs");
    }
    let inputs = vec![
        hash.hash(
            &nat_to_limbs(&group.g, 32, 64)
                .unwrap()
                .into_iter()
                .chain(nat_to_limbs(&group.m, 32, 64).unwrap().into_iter())
                .collect::<Vec<E::Fr>>(),
        ),
        hash.hash(&nat_to_limbs(&inputs.initial_state.digest(), 32, 64).unwrap()),
        hash.hash(&nat_to_limbs(&inputs.final_state.digest(), 32, 64).unwrap()),
    ];

    let init_end = Instant::now();
    if args.flag_verbose {
        println!("Init time: {:?}", init_end - init_start);
    }

    if args.flag_verbose {
        println!("Generating prover and verifier keys");
    }
    let param_start = Instant::now();
    let params = {
        if let Some(ref path) = args.flag_iparams {
            if args.flag_verbose {
                println!("Loading...");
            }

            let mut f = std::fs::File::open(path).expect("Error opening params");
            let p = Parameters::read(&mut f, false).expect("Error parsing params");
            p
        } else {
            let p = generate_random_parameters(empty_circuit, rng);
            if args.flag_verbose {
                println!("Params gen is okay: {:#?}", p.is_ok());
            }
            assert!(p.is_ok());
            p.unwrap()
        }
    };
    if let Some(ref path) = args.flag_oparams {
        let mut f = std::fs::File::create(path).expect("Error opening param output file");
        params.write(&mut f).expect("Error writing params");
        std::process::exit(0);
    }
    let pvk = prepare_verifying_key(&params.vk);
    let param_end = Instant::now();

    if args.flag_verbose {
        println!("Generating proof");
    }

    let (proof, prover_synth_time, prover_crypto_time) =
        create_random_proof(circuit, &params, rng).unwrap();
    if args.flag_verbose {
        println!("Proof generation successful? true");
    }

    let verifier_start = Instant::now();
    let result = verify_proof(&pvk, &proof, &inputs);
    let verifier_end = Instant::now();
    if args.flag_verbose {
        println!("Verified? {:?}", result.is_ok(),);
    }
    assert!(result.is_ok());

    TimeReport {
        init: init_end - init_start,
        param_gen: param_end - param_start,
        prover_synth: prover_synth_time,
        prover_crypto: prover_crypto_time,
        verifier: verifier_end - verifier_start,
    }
}

fn merkle_bench<E: Engine, H: Hasher<F = E::Fr> + CircuitHasher<E = E>>(
    args: &Args,
    hash: H,
) -> TimeReport {
    let rng = &mut thread_rng();

    if args.flag_verbose {
        println!("Initializing accumulators, circuits");
    }
    let init_start = Instant::now();
    let merkle_params = MerkleSetBenchParams {
        item_size: ELEMENT_SIZE,
        n_swaps: args.arg_transactions,
        hash: hash.clone(),
        depth: args.arg_capacity,
        verbose: args.flag_verbose,
    };
    let empty_circuit = MerkleSetBench {
        inputs: None,
        params: merkle_params.clone(),
    };

    // Create a groth16 proof with our parameters.
    let merkle_inputs = MerkleSetBenchInputs::from_counts(
        if args.flag_full {
            (1 << args.arg_capacity) - args.arg_transactions
        } else {
            0
        },
        args.arg_transactions,
        ELEMENT_SIZE,
        hash,
        args.arg_capacity,
    );

    let circuit = MerkleSetBench {
        inputs: Some(merkle_inputs),
        params: merkle_params,
    };

    let ins = circuit.inputs.as_ref().unwrap();
    let mut initial_set = ins.initial_state.clone();
    let mut final_set = {
        let tt = std::time::Instant::now();
        let mut t = initial_set.clone();
        t.swap_all(ins.to_remove.clone(), ins.to_insert.clone());
        if verbose::in_verbose_mode() {
            println!("Digest update time: {}s", tt.elapsed().as_secs_f64());
        }
        t
    };
    let inputs: Vec<E::Fr> = vec![initial_set.digest(), final_set.digest()];

    let init_end = Instant::now();

    if args.flag_verbose {
        println!("Generating prover and verifier keys");
    }
    let param_start = Instant::now();
    let params = {
        let p = generate_random_parameters(empty_circuit, rng);
        if args.flag_verbose {
            println!("Params gen is okay: {:#?}", p.is_ok());
        }
        assert!(p.is_ok());
        p.unwrap()
    };
    let pvk = prepare_verifying_key(&params.vk);
    let param_end = Instant::now();

    if args.flag_verbose {
        println!("Generating proof");
    }

    let (proof, prover_synth_time, prover_crypto_time) =
        create_random_proof(circuit, &params, rng).unwrap();
    if args.flag_verbose {
        println!("Proof generation successful? true");
    }

    let verifier_start = Instant::now();
    let result = verify_proof(&pvk, &proof, &inputs);
    let verifier_end = Instant::now();
    if args.flag_verbose {
        println!("Verified? {:?}", result.is_ok(),);
    }
    assert!(result.is_ok());

    TimeReport {
        init: init_end - init_start,
        param_gen: param_end - param_start,
        prover_synth: prover_synth_time,
        prover_crypto: prover_crypto_time,
        verifier: verifier_end - verifier_start,
    }
}
