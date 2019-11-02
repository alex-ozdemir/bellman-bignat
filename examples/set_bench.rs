extern crate bellman_bignat;
extern crate docopt;
extern crate num_bigint;
extern crate rand;
extern crate sapling_crypto;
extern crate serde;

use bellman_bignat::bench::{ConstraintCounter, ConstraintProfiler};
use bellman_bignat::group::RsaQuotientGroup;
use bellman_bignat::hash::Hasher;
use bellman_bignat::hash::circuit::CircuitHasher;
use bellman_bignat::hash::hashes::{Pedersen, BabyPedersen, Poseidon, Mimc};
use bellman_bignat::set::merkle::{MerkleSetBench, MerkleSetBenchInputs, MerkleSetBenchParams};
use bellman_bignat::set::rsa::{SetBench, SetBenchInputs, SetBenchParams};
use docopt::Docopt;
use num_bigint::BigUint;
use sapling_crypto::bellman::pairing::bn256::Bn256;
use sapling_crypto::bellman::pairing::Engine;
use sapling_crypto::bellman::Circuit;
use serde::Deserialize;

use std::str::FromStr;

const USAGE: &str = "
Set Benchmarker

Usage:
  set_bench [options] rsa <transactions> <capacity>
  set_bench [options] merkle <transactions> <capacity>
  set_bench (-h | --help)
  set_bench --version

Options:
  -p --profile  Profile constraints, instead of just counting them
                Emits JSON to stdout
  -h --help     Show this screen.
  --hash HASH   The hash function to use [default: poseidon]
                Valid values: poseidon, mimc, pedersen, babypedersen
  --version     Show version.
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
    BabyPedersen,
}

#[derive(Debug, Deserialize)]
struct Args {
    arg_transactions: usize,
    arg_capacity: usize,
    flag_profile: bool,
    flag_hash: Hashes,
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
            match args.flag_hash {
                Hashes::Poseidon => rsa_bench(args.arg_transactions, args.arg_capacity, args.flag_profile, Poseidon::default()),
                Hashes::Mimc => rsa_bench::<Bn256, _>(args.arg_transactions, args.arg_capacity, args.flag_profile, Mimc::default()),
                Hashes::Pedersen => rsa_bench(args.arg_transactions, args.arg_capacity, args.flag_profile, Pedersen::default()),
                Hashes::BabyPedersen => rsa_bench(args.arg_transactions, args.arg_capacity, args.flag_profile, BabyPedersen::default()),
            }
        )
    } else if args.cmd_merkle {
        (
            "merkle",
            match args.flag_hash {
                Hashes::Poseidon => merkle_bench(args.arg_transactions, args.arg_capacity, args.flag_profile, Poseidon::default()),
                Hashes::Mimc => merkle_bench::<Bn256, _>(args.arg_transactions, args.arg_capacity, args.flag_profile, Mimc::default()),
                Hashes::Pedersen => merkle_bench(args.arg_transactions, args.arg_capacity, args.flag_profile, Pedersen::default()),
                Hashes::BabyPedersen => merkle_bench(args.arg_transactions, args.arg_capacity, args.flag_profile, BabyPedersen::default()),
            }
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

fn rsa_bench<E: Engine, H: Hasher<F = E::Fr> + CircuitHasher<E = E>>(t: usize, _c: usize, profile: bool, hash: H) -> usize {
    let group = RsaQuotientGroup {
        g: BigUint::from(2usize),
        m: BigUint::from_str(RSA_2048).unwrap(),
    };

    let circuit = SetBench {
        inputs: Some(SetBenchInputs::from_counts(
            0,
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
            n_bits_challenge: 128,
            n_bits_base: RSA_SIZE,
            item_size: ELEMENT_SIZE,
            n_inserts: t,
            n_removes: t,
            hasher: hash,
            verbose: false,
        },
    };

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

fn merkle_bench<E: Engine, H: Hasher<F = E::Fr> + CircuitHasher<E = E>>(t: usize, c: usize, profile: bool, hash: H) -> usize {

    let circuit = MerkleSetBench {
        inputs: Some(MerkleSetBenchInputs::from_counts(
            0,
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
