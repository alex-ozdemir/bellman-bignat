extern crate bellman_bignat;
extern crate num_bigint;
extern crate rand;
extern crate sapling_crypto;

use bellman_bignat::bignat::nat_to_limbs;
use bellman_bignat::group::RsaGroup;
use bellman_bignat::set::int_set::NaiveExpSet;
use bellman_bignat::set::GenSet;
use bellman_bignat::set::rsa::{SetBench, SetBenchInputs, SetBenchParams};
use num_bigint::BigUint;
use sapling_crypto::poseidon::bn256::Bn256PoseidonParams;

use std::rc::Rc;
use std::str::FromStr;
use std::time::Instant;

// From https://en.wikipedia.org/wiki/RSA_numbers#RSA-2048
const RSA_2048: &str = "25195908475657893494027183240048398571429282126204032027777137836043662020707595556264018525880784406918290641249515082189298559149176184502808489120072844992687392807287776735971418347270261896375014971824691165077613379859095700097330459748808428401797429100642458691817195118746121515172654632282216869987549182422433637259085141865462043576798423387184774447920739934236584823824281198163815010674810451660377306056201619676256133844143603833904414952634432190114657544454178424020924616515723350778707749817125772467962926386356373289912154831438167899885040445364023527381951378636564391212010397122822120720357";
const RSA_SIZE: usize = 2048;
const ELEMENT_SIZE: usize = 5;

fn main() {
    color_backtrace::install();

    let n_swaps = std::env::args()
        .nth(1)
        .and_then(|a| usize::from_str(&a).ok())
        .expect("Provide the number of transactions as the first argument");

    let hash = Rc::new(Bn256PoseidonParams::new::<
        sapling_crypto::group_hash::Keccak256Hasher,
    >());
    use rand::thread_rng;

    use sapling_crypto::bellman::groth16::{
        create_random_proof, generate_random_parameters, prepare_verifying_key, verify_proof,
    };

    let group = RsaGroup {
        g: BigUint::from(2usize),
        m: BigUint::from_str(RSA_2048).unwrap(),
    };
    let rng = &mut thread_rng();

    let generate_params_start = Instant::now();

    let params = {
        let c = SetBench::<Bn256, NaiveExpSet<RsaGroup>> {
            inputs: None,
            params: SetBenchParams {
                group: group.clone(),
                limb_width: 32,
                n_bits_elem: RSA_SIZE,
                n_bits_challenge: 128,
                n_bits_base: RSA_SIZE,
                item_size: ELEMENT_SIZE,
                n_inserts: n_swaps,
                n_removes: n_swaps,
                hash: hash.clone(),
                verbose: true,
            },
        };
        let p = generate_random_parameters(c, rng);
        println!("Params are okay: {:#?}", p.is_ok());
        p.unwrap()
    };

    let generate_params_end = Instant::now();

    println!(
        "Done with parameters, duration {:?}",
        generate_params_end - generate_params_start
    );

    let pvk = prepare_verifying_key(&params.vk);
    println!("Done with key");

    // Create a groth16 proof with our parameters.
    let circuit = SetBench {
        inputs: Some(SetBenchInputs::from_counts(
            0,
            n_swaps,
            n_swaps,
            ELEMENT_SIZE,
            hash.clone(),
            RSA_SIZE,
            32,
            RsaGroup {
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
            n_inserts: n_swaps,
            n_removes: n_swaps,
            hash,
            verbose: true,
        },
    };

    let ins = circuit.inputs.as_ref().unwrap();
    let initial_set = ins.initial_state.clone();
    let final_set = {
        let mut t = initial_set.clone();
        t.swap_all(ins.to_remove.clone(), ins.to_insert.clone());
        t
    };

    let prover_start = Instant::now();

    let proof = create_random_proof(circuit, &params, rng).unwrap();

    let prover_end = Instant::now();
    println!("Done with proof, duration: {:?}", prover_end - prover_start);
    use sapling_crypto::bellman::pairing::bn256::Bn256;
    use sapling_crypto::bellman::pairing::ff::ScalarEngine;
    let mut inputs: Vec<<Bn256 as ScalarEngine>::Fr> = nat_to_limbs(&group.g, 32, 64).unwrap();
    inputs.extend(nat_to_limbs::<<Bn256 as ScalarEngine>::Fr>(&group.m, 32, 64).unwrap());
    inputs.extend(
        nat_to_limbs::<<Bn256 as ScalarEngine>::Fr>(&initial_set.digest(), 32, 64).unwrap(),
    );
    inputs
        .extend(nat_to_limbs::<<Bn256 as ScalarEngine>::Fr>(&final_set.digest(), 32, 64).unwrap());

    println!("verified {:?}", verify_proof(&pvk, &proof, &inputs));
}
