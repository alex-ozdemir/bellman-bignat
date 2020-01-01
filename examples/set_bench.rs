extern crate bellman_bignat;
extern crate docopt;
extern crate num_bigint;
extern crate rand;
extern crate sapling_crypto;
extern crate serde;

use bellman_bignat::bench::{ConstraintCounter, ConstraintProfiler, WitnessTimer};
use bellman_bignat::group::RsaQuotientGroup;
use bellman_bignat::hash::circuit::CircuitHasher;
use bellman_bignat::hash::hashes::{Mimc, Pedersen, Poseidon, Sha256};
use bellman_bignat::hash::Hasher;
use bellman_bignat::set::merkle::{MerkleSetBench, MerkleSetBenchInputs, MerkleSetBenchParams};
use bellman_bignat::set::rsa::{SetBench, SetBenchInputs, SetBenchParams};
use docopt::Docopt;
use num_bigint::BigUint;
use sapling_crypto::bellman::pairing::bls12_381::Bls12;
use sapling_crypto::bellman::pairing::Engine;
use sapling_crypto::bellman::Circuit;
use serde::Deserialize;

use std::str::FromStr;
use std::convert::TryInto;

const USAGE: &str = "
Set Benchmarker

Usage:
  set_bench [options] rsa <transactions> <capacity>
  set_bench [options] merkle <transactions> <capacity>
  set_bench (-h | --help)
  set_bench --version

Options:
  -s --synth TY  Sythesizer to use [default: counter]
                 Valid values: counter, timer, profiler
                 profiler: emits JSON to stdout
                 counter: emits CSV w/ constraints to stdout
                 timer: emits CSV w/ times to stdout
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

#[derive(Debug, Deserialize, PartialEq, Clone, Copy)]
enum Synthesizer {
    Counter,
    Timer,
    Profiler,
}

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
    flag_synth: Synthesizer,
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
    let (set, cost) = if args.cmd_rsa {
        (
            "rsa",
            match args.flag_hash {
                Hashes::Poseidon => rsa_bench::<Bls12, _>(
                    args.arg_transactions,
                    args.arg_capacity,
                    args.flag_full,
                    args.flag_synth,
                    Poseidon::default(),
                ),
                Hashes::Mimc => rsa_bench::<Bls12, _>(
                    args.arg_transactions,
                    args.arg_capacity,
                    args.flag_full,
                    args.flag_synth,
                    Mimc::default(),
                ),
                Hashes::Pedersen => rsa_bench::<Bls12, _>(
                    args.arg_transactions,
                    args.arg_capacity,
                    args.flag_full,
                    args.flag_synth,
                    Pedersen::default(),
                ),
                Hashes::Sha => rsa_bench::<Bls12, _>(
                    args.arg_transactions,
                    args.arg_capacity,
                    args.flag_full,
                    args.flag_synth,
                    Sha256::default(),
                ),
            },
        )
    } else if args.cmd_merkle {
        (
            "merkle",
            match args.flag_hash {
                Hashes::Poseidon => merkle_bench::<Bls12, _>(
                    args.arg_transactions,
                    args.arg_capacity,
                    args.flag_full,
                    args.flag_synth,
                    Poseidon::default(),
                ),
                Hashes::Mimc => merkle_bench::<Bls12, _>(
                    args.arg_transactions,
                    args.arg_capacity,
                    args.flag_full,
                    args.flag_synth,
                    Mimc::default(),
                ),
                Hashes::Pedersen => merkle_bench::<Bls12, _>(
                    args.arg_transactions,
                    args.arg_capacity,
                    args.flag_full,
                    args.flag_synth,
                    Pedersen::default(),
                ),
                Hashes::Sha => merkle_bench::<Bls12, _>(
                    args.arg_transactions,
                    args.arg_capacity,
                    args.flag_full,
                    args.flag_synth,
                    Sha256::default(),
                ),
            },
        )
    } else {
        panic!("Unknown command")
    };
    if args.flag_synth != Synthesizer::Profiler {
        println!(
            "{},{:?},{},{},{}",
            set, args.flag_hash, args.arg_transactions, args.arg_capacity, cost
        );
    }
}

fn rsa_bench<E: Engine, H: Hasher<F = E::Fr> + CircuitHasher<E = E>>(
    t: usize,
    c: usize,
    full: bool,
    synth: Synthesizer,
    hash: H,
) -> usize {
    let group = RsaQuotientGroup {
        g: BigUint::from(2usize),
        m: BigUint::from_str(RSA_2048).unwrap(),
    };

    let n_untouched = if full { (1usize << c).saturating_sub(t) } else { 0 };
    let circuit = SetBench {
        inputs: Some(SetBenchInputs::from_counts(
            n_untouched,
            t,
            t,
            ELEMENT_SIZE,
            hash.clone(),
            RSA_SIZE,
            32,
            RsaQuotientGroup {
                g: BigUint::from(2usize),
                m: BigUint::from_str(RSA_2048).unwrap(),
            },
        )),
        params: SetBenchParams {
            group: group.clone(),
            limb_width: 32,
            n_bits_elem: RSA_SIZE,
            n_bits_challenge: 256,
            n_bits_base: RSA_SIZE,
            item_size: ELEMENT_SIZE,
            n_inserts: t,
            n_removes: t,
            hasher: hash,
            verbose: false,
        },
    };

    match synth {
        Synthesizer::Profiler => {
            let mut cs = ConstraintProfiler::new();
            circuit.synthesize(&mut cs).expect("synthesis failed");
            cs.emit_as_json(&mut std::io::stdout()).unwrap();
            cs.num_constraints()
        }
        Synthesizer::Timer => {
            let mut cs = WitnessTimer::new();
            circuit.synthesize(&mut cs).expect("synthesis failed");
            cs.elapsed().as_millis().try_into().unwrap()
        }
        Synthesizer::Counter => {
            let mut cs = ConstraintCounter::new();
            circuit.synthesize(&mut cs).expect("synthesis failed");
            cs.num_constraints()
        }
    }
}

fn merkle_bench<E: Engine, H: Hasher<F = E::Fr> + CircuitHasher<E = E>>(
    t: usize,
    c: usize,
    full: bool,
    synth: Synthesizer,
    hash: H,
) -> usize {
    let n_untouched = if full { (1usize << c).saturating_sub(t) } else { 0 };
    let circuit = MerkleSetBench {
        inputs: Some(MerkleSetBenchInputs::from_counts(
            n_untouched,
            t,
            ELEMENT_SIZE,
            hash.clone(),
            c,
        )),
        params: MerkleSetBenchParams {
            item_size: ELEMENT_SIZE,
            n_swaps: t,
            hash,
            verbose: false,
            depth: c,
        },
    };

    match synth {
        Synthesizer::Profiler => {
            let mut cs = ConstraintProfiler::new();
            circuit.synthesize(&mut cs).expect("synthesis failed");
            cs.emit_as_json(&mut std::io::stdout()).unwrap();
            cs.num_constraints()
        }
        Synthesizer::Timer => {
            let mut cs = WitnessTimer::new();
            circuit.synthesize(&mut cs).expect("synthesis failed");
            cs.elapsed().as_millis().try_into().unwrap()
        }
        Synthesizer::Counter => {
            let mut cs = ConstraintCounter::new();
            circuit.synthesize(&mut cs).expect("synthesis failed");
            cs.num_constraints()
        }
    }
}
