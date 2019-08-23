extern crate bellman_bignat;
extern crate num_bigint;
extern crate rand;
extern crate sapling_crypto;

use bellman_bignat::rollup::{Rollup, RollupParams, RollupInputs};
use bellman_bignat::rsa_set::{
    NaiveRsaSetBackend, RsaGroup,
};
use num_bigint::BigUint;
use sapling_crypto::poseidon::bn256::Bn256PoseidonParams;

use std::str::FromStr;

// From https://en.wikipedia.org/wiki/RSA_numbers#RSA-2048
const RSA_2048: &str = "25195908475657893494027183240048398571429282126204032027777137836043662020707595556264018525880784406918290641249515082189298559149176184502808489120072844992687392807287776735971418347270261896375014971824691165077613379859095700097330459748808428401797429100642458691817195118746121515172654632282216869987549182422433637259085141865462043576798423387184774447920739934236584823824281198163815010674810451660377306056201619676256133844143603833904414952634432190114657544454178424020924616515723350778707749817125772467962926386356373289912154831438167899885040445364023527381951378636564391212010397122822120720357";
// From my machine (openssl)
const RSA_512: &str = "11834783464130424096695514462778870280264989938857328737807205623069291535525952722847913694296392927890261736769191982212777933726583565708193466779811767";

const CHALLENGE: &str = "274481455456098291870407972073878126369";

fn main() {
    color_backtrace::install();

    let hash = Bn256PoseidonParams::new::<sapling_crypto::group_hash::Keccak256Hasher>();
    let circuit = Rollup {
        inputs: Some(RollupInputs::new(
            &[],
            &[&["0", "1", "2", "3", "4"]],
            &[&["0", "1", "2", "3", "5"]],
            &hash,
            1024,
        )),
        params: RollupParams {
            group: RsaGroup {
                g: BigUint::from(2usize),
                m: BigUint::from_str(RSA_2048).unwrap(),
            },
            limb_width: 32,
            n_bits_elem: 1024,
            n_bits_challenge: 128,
            n_bits_base: 2048,
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
                group: RsaGroup {
                    g: BigUint::from(2usize),
                    m: BigUint::from_str(RSA_2048).unwrap(),
                },
                limb_width: 32,
                n_bits_elem: 1024,
                n_bits_challenge: 128,
                n_bits_base: 2048,
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
