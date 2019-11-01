extern crate bellman_bignat;
extern crate docopt;
extern crate num_bigint;
extern crate rand;
extern crate sapling_crypto;
extern crate serde;

use bellman_bignat::bench::{ConstraintCounter, ConstraintProfiler};
use bellman_bignat::bignat::nat_to_limbs;
use bellman_bignat::group::RsaQuotientGroup;
use bellman_bignat::hash::hashes::Poseidon;
use bellman_bignat::set::merkle::{MerkleSetBench, MerkleSetBenchInputs, MerkleSetBenchParams};
use bellman_bignat::set::GenSet;
use bellman_bignat::set::rsa::{SetBench, SetBenchInputs, SetBenchParams};
use docopt::Docopt;
use num_bigint::BigUint;
use sapling_crypto::bellman::pairing::bn256::Bn256;
use sapling_crypto::bellman::pairing::ff::ScalarEngine;
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
  --version     Show version.
";

// From https://en.wikipedia.org/wiki/RSA_numbers#RSA-2048
const RSA_2048: &str = "25195908475657893494027183240048398571429282126204032027777137836043662020707595556264018525880784406918290641249515082189298559149176184502808489120072844992687392807287776735971418347270261896375014971824691165077613379859095700097330459748808428401797429100642458691817195118746121515172654632282216869987549182422433637259085141865462043576798423387184774447920739934236584823824281198163815010674810451660377306056201619676256133844143603833904414952634432190114657544454178424020924616515723350778707749817125772467962926386356373289912154831438167899885040445364023527381951378636564391212010397122822120720357";
const RSA_SIZE: usize = 2048;
const ELEMENT_SIZE: usize = 5;

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
    let group = RsaQuotientGroup {
        g: BigUint::from(2usize),
        m: BigUint::from_str(RSA_2048).unwrap(),
    };

    let circuit = SetBench::<Poseidon<Bn256>, _> {
        inputs: Some(SetBenchInputs::from_counts(
            0,
            t,
            t,
            ELEMENT_SIZE,
            Poseidon::default(),
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
            hasher: Poseidon::default(),
            verbose: false,
        },
    };

    let ins = circuit.inputs.as_ref().unwrap();
    let initial_set = ins.initial_state.clone();
    let final_set = {
        let mut t = initial_set.clone();
        t.swap_all(ins.to_remove.clone(), ins.to_insert.clone());
        t
    };

    let mut inputs: Vec<<Bn256 as ScalarEngine>::Fr> = nat_to_limbs(&group.g, 32, 64).unwrap();
    inputs.extend(nat_to_limbs::<<Bn256 as ScalarEngine>::Fr>(&group.m, 32, 64).unwrap());
    inputs.extend(
        nat_to_limbs::<<Bn256 as ScalarEngine>::Fr>(&initial_set.digest(), 32, 64).unwrap(),
    );
    inputs
        .extend(nat_to_limbs::<<Bn256 as ScalarEngine>::Fr>(&final_set.digest(), 32, 64).unwrap());

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

    let circuit = MerkleSetBench {
        inputs: Some(MerkleSetBenchInputs::from_counts(
            0,
            t,
            ELEMENT_SIZE,
            Poseidon::default(),
            c,
        )),
        params: MerkleSetBenchParams {
            item_size: ELEMENT_SIZE,
            n_swaps: t,
            hash: Poseidon::default(),
            verbose: false,
            depth: c,
        },
    };

    let ins = circuit.inputs.as_ref().unwrap();
    let initial_set = ins.initial_state.clone();
    let _final_set = {
        let mut t = initial_set.clone();
        t.swap_all(ins.to_remove.clone(), ins.to_insert.clone());
        t
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
