extern crate bellman_bignat;
extern crate docopt;
extern crate rand;
extern crate rug;
extern crate sapling_crypto;
extern crate serde;

use bellman_bignat::mp::bignat::{BigNat, BigNatParams};
use bellman_bignat::util::bench::ConstraintCounter;
use docopt::Docopt;
use rand::thread_rng;
use rug::Integer;
use sapling_crypto::bellman::groth16::{
    create_random_proof, generate_random_parameters, prepare_verifying_key, verify_proof,
};
use sapling_crypto::bellman::pairing::bls12_381::Bls12;
use sapling_crypto::bellman::pairing::ff::Field;
use sapling_crypto::bellman::pairing::ff::ScalarEngine;
use sapling_crypto::bellman::pairing::Engine;
use sapling_crypto::bellman::{Circuit, ConstraintSystem};
use sapling_crypto::circuit::Assignment;
use serde::Deserialize;

const RSA_2048: &str = "25195908475657893494027183240048398571429282126204032027777137836043662020707595556264018525880784406918290641249515082189298559149176184502808489120072844992687392807287776735971418347270261896375014971824691165077613379859095700097330459748808428401797429100642458691817195118746121515172654632282216869987549182422433637259085141865462043576798423387184774447920739934236584823824281198163815010674810451660377306056201619676256133844143603833904414952634432190114657544454178424020924616515723350778707749817125772467962926386356373289912154831438167899885040445364023527381951378636564391212010397122822120720357";
const RSA_256: &str =
    "106248002751926319395891834899006256764828172975092526450029596908411425878871";

const USAGE: &str = "
Set Benchmarker

Usage:
  set_bench [options]
  set_bench (-h | --help)
  set_bench --version

Options:
  -l --limb-width N   Limb size to use [default: 16]
  -h --help           Show this screen.
  --version           Show version.
";

#[derive(Clone, Debug)]
struct RsaSignatureExponentiation {
    modulus: Option<Integer>,
    base: Option<Integer>,
    result: Option<Integer>,
    params: BigNatParams,
}

impl<E> Circuit<E> for RsaSignatureExponentiation
where
    E: Engine,
{
    fn synthesize<CS: ConstraintSystem<E>>(
        self,
        cs: &mut CS,
    ) -> Result<(), sapling_crypto::bellman::SynthesisError> {
        let mut modulus = BigNat::alloc_from_nat(
            cs.namespace(|| "modulus"),
            || self.modulus.get().cloned(),
            self.params.limb_width,
            self.params.n_limbs,
        )?;
        modulus.params.min_bits = self.params.min_bits;
        let base = BigNat::alloc_from_nat(
            cs.namespace(|| "modulus"),
            || self.base.get().cloned(),
            self.params.limb_width,
            self.params.n_limbs,
        )?;
        let result = BigNat::alloc_from_nat(
            cs.namespace(|| "result"),
            || self.result.get().cloned(),
            self.params.limb_width,
            self.params.n_limbs,
        )?;
        let mut pow2 = base.clone();
        for i in 0..16 {
            pow2 = pow2
                .mult_mod(cs.namespace(|| format!("mult{}", i)), &pow2, &modulus)?
                .1;
        }
        let actual_result = pow2
            .mult_mod(cs.namespace(|| "last_mult"), &base, &modulus)?
            .1;
        result.equal(cs.namespace(|| "eq"), &actual_result)?;
        Ok(())
    }
}

#[derive(Debug, Deserialize)]
struct Args {
    flag_limb_width: usize,
}

fn main() {
    color_backtrace::install();
    let args: Args = Docopt::new(USAGE)
        .and_then(|d| d.deserialize())
        .unwrap_or_else(|e| e.exit());
    let mut ct = ConstraintCounter::new();
    let modulus = Integer::from_str_radix(RSA_2048, 10).unwrap();
    let size = modulus.significant_bits() as usize;
    let base = Integer::from(2);
    let exp = Integer::from(0x10001);
    let result = base.clone().pow_mod(&exp, &modulus).unwrap();
    let ckt = RsaSignatureExponentiation {
        modulus: Some(modulus),
        base: Some(base),
        result: Some(result),
        params: BigNatParams {
            min_bits: size,
            max_word: Integer::from(1u8) << args.flag_limb_width as u32 - 1,
            limb_width: args.flag_limb_width,
            n_limbs: (size - 1) / args.flag_limb_width + 1,
        },
    };
    <RsaSignatureExponentiation as Circuit<Bls12>>::synthesize(ckt.clone(), &mut ct).unwrap();
    println!("constraints: {}", ct.num_constraints());
    let rng = &mut thread_rng();
    let t = std::time::Instant::now();
    let params = generate_random_parameters::<Bls12, _, _>(ckt.clone(), rng).unwrap();
    println!("setup: {}ns", t.elapsed().as_nanos());
    let t = std::time::Instant::now();
    let proof = create_random_proof(ckt.clone(), &params, rng).unwrap();
    println!("prove: {}ns", t.elapsed().as_nanos());
    let pvk = prepare_verifying_key(&params.vk);
    let t = std::time::Instant::now();
    assert!(verify_proof(&pvk, &proof, &[]).unwrap());
    println!("verify: {}ns", t.elapsed().as_nanos());
}
