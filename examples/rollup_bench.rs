extern crate bellman_bignat;
extern crate docopt;
extern crate num_bigint;
extern crate rand;
extern crate sapling_crypto;
extern crate serde;

use bellman_bignat::bench::{ConstraintCounter, ConstraintProfiler};
use bellman_bignat::rollup::rsa::RollupBench;
use docopt::Docopt;
use sapling_crypto::alt_babyjubjub::AltJubjubBn256;
use sapling_crypto::bellman::pairing::bn256::Bn256;
use sapling_crypto::bellman::Circuit;
use sapling_crypto::group_hash::Keccak256Hasher;
use sapling_crypto::poseidon::bn256::Bn256PoseidonParams;
use serde::Deserialize;

const USAGE: &str = "
Rollup Benchmarker

Usage:
  rollup_bench [options] rsa <transactions> <capacity>
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

fn rsa_bench(t: usize, c: usize, profile: bool) -> usize {
    let circuit = RollupBench::<Bn256>::from_counts(
        1 << c,
        t,
        AltJubjubBn256::new(),
        Bn256PoseidonParams::new::<Keccak256Hasher>(),
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
