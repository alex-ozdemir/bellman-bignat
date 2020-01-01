extern crate bellman_bignat;
extern crate docopt;
extern crate num_bigint;
extern crate rand;
extern crate sapling_crypto;
extern crate serde;

use bellman_bignat::util::bench::{ConstraintCounter, ConstraintProfiler};
use bellman_bignat::rollup::{rsa, merkle};
use bellman_bignat::hash::hashes::Poseidon;
use docopt::Docopt;
use sapling_crypto::jubjub::JubjubBls12;
use sapling_crypto::bellman::pairing::bls12_381::Bls12;
use sapling_crypto::bellman::Circuit;
use serde::Deserialize;

const USAGE: &str = "
Rollup Benchmarker

Usage:
  rollup_bench [options] rsa <transactions> <capacity>
  rollup_bench [options] merkle <transactions> <capacity>
  rollup_bench (-h | --help)
  rollup_bench --version

Options:
  -p --profile  Profile constraints, instead of just counting them
                Emits JSON to stdout
  -h --help     Show this screen.
  --version     Show version.
";

#[derive(Debug, Deserialize)]
struct Args {
    arg_transactions: usize,
    arg_capacity: usize,
    flag_profile: bool,
    cmd_rsa: bool,
    cmd_merkle: bool,
}

fn main() {
    color_backtrace::install();
    let args: Args = Docopt::new(USAGE)
        .and_then(|d| d.deserialize())
        .unwrap_or_else(|e| e.exit());
    let (set, constraints) = if args.cmd_rsa {
        (
            "rsa",
            rsa_bench(args.arg_transactions, args.arg_capacity, args.flag_profile),
        )
    } else if args.cmd_merkle {
        (
            "merkle",
            merkle_bench(args.arg_transactions, args.arg_capacity, args.flag_profile),
        )
    } else {
        panic!("Unknown command")
    };
    if !args.flag_profile {
        println!(
            "{},{},{},{}",
            set, args.arg_transactions, args.arg_capacity, constraints
        );
    }
}

fn rsa_bench(t: usize, _c: usize, profile: bool) -> usize {
    let circuit = rsa::RollupBench::<Bls12, Poseidon<Bls12>>::from_counts(
        t, // Use `t` in place of `c` for sparse-ness.
        t,
        JubjubBls12::new(),
        Poseidon::default(),
    );

    if profile {
        let mut cs = ConstraintProfiler::new();
        circuit.synthesize(&mut cs).expect("synthesis failed");
        cs.emit_as_json(&mut std::io::stdout()).unwrap();
        cs.num_constraints()
    } else {
        let mut cs = ConstraintCounter::new();
        circuit.synthesize(&mut cs).expect("synthesis failed");
        cs.num_constraints()
    }
}

fn merkle_bench(t: usize, c: usize, profile: bool) -> usize {
    let circuit = merkle::RollupBench::<Bls12, _>::from_counts(
        c,
        t,
        JubjubBls12::new(),
        Poseidon::default(),
    );

    if profile {
        let mut cs = ConstraintProfiler::new();
        circuit.synthesize(&mut cs).expect("synthesis failed");
        cs.emit_as_json(&mut std::io::stdout()).unwrap();
        cs.num_constraints()
    } else {
        let mut cs = ConstraintCounter::new();
        circuit.synthesize(&mut cs).expect("synthesis failed");
        cs.num_constraints()
    }
}
