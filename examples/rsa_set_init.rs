extern crate bellman_bignat;
extern crate docopt;
extern crate rand;
extern crate sapling_crypto;
extern crate serde;

use bellman_bignat::group::RsaQuotientGroup;
use bellman_bignat::hash::circuit::CircuitHasher;
use bellman_bignat::hash::hashes::Poseidon;
use bellman_bignat::hash::Hasher;
use bellman_bignat::set::int_set_par::ParallelExpSet;
use bellman_bignat::set::rsa::SetBenchInputs;
use bellman_bignat::util::verbose;
use docopt::Docopt;
use sapling_crypto::bellman::pairing::bls12_381::Bls12;
use sapling_crypto::bellman::pairing::Engine;
use serde::Deserialize;

const USAGE: &str = "
RSA Set Initialization

Usage:
  rsa_set_init <transactions> <capacity>
  rsa_set_init (-h | --help)

Options:
  -h --help      Show this screen.
";

// From https://en.wikipedia.org/wiki/RSA_numbers#RSA-2048
const RSA_2048: &str = "25195908475657893494027183240048398571429282126204032027777137836043662020707595556264018525880784406918290641249515082189298559149176184502808489120072844992687392807287776735971418347270261896375014971824691165077613379859095700097330459748808428401797429100642458691817195118746121515172654632282216869987549182422433637259085141865462043576798423387184774447920739934236584823824281198163815010674810451660377306056201619676256133844143603833904414952634432190114657544454178424020924616515723350778707749817125772467962926386356373289912154831438167899885040445364023527381951378636564391212010397122822120720357";
const RSA_SIZE: usize = 2048;
const ELEMENT_SIZE: usize = 5;

#[derive(Debug, Deserialize)]
struct Args {
    arg_transactions: usize,
    arg_capacity: usize,
}

fn main() {
    color_backtrace::install();
    let args: Args = Docopt::new(USAGE)
        .and_then(|d| d.deserialize())
        .unwrap_or_else(|e| e.exit());
    verbose::set_verbose_mode(true);
    rsa_bench::<Bls12, _>(&args, Poseidon::default());
}

fn rsa_bench<E: Engine, H: Hasher<F = E::Fr> + CircuitHasher<E = E>>(args: &Args, hash: H) {
    println!("Initializing accumulators, circuits");
    let n_untouched = (1usize << args.arg_capacity).saturating_sub(args.arg_transactions);

    println!("Constructing initial and final states");
    let _inputs = SetBenchInputs::<_, ParallelExpSet<RsaQuotientGroup>>::from_counts(
        n_untouched,
        args.arg_transactions,
        args.arg_transactions,
        ELEMENT_SIZE,
        hash.clone(),
        RSA_SIZE,
        32,
        RsaQuotientGroup::from_strs("2", RSA_2048),
    );
    println!("Done");
}
