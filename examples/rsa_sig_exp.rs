extern crate bellman_bignat;
extern crate docopt;
extern crate rug;
extern crate sapling_crypto;
extern crate serde;

use bellman_bignat::mp::bignat::{BigNat, BigNatParams};
use bellman_bignat::util::bench::ConstraintCounter;
use docopt::Docopt;
use rug::Integer;
use sapling_crypto::bellman::pairing::bls12_381::Bls12;
use sapling_crypto::bellman::pairing::Engine;
use sapling_crypto::bellman::{Circuit, ConstraintSystem};
use sapling_crypto::circuit::Assignment;
use serde::Deserialize;

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
        modulus.params.min_bits = 2048;
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
                .0;
        }
        let actual_result = pow2
            .mult_mod(cs.namespace(|| "last_mult"), &base, &modulus)?
            .0;
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
    let ckt = RsaSignatureExponentiation {
        modulus: None,
        base: None,
        result: None,
        params: BigNatParams {
            min_bits: 2048,
            max_word: Integer::from(1u8) << args.flag_limb_width as u32 - 1,
            limb_width: args.flag_limb_width,
            n_limbs: (2048 - 1) / args.flag_limb_width + 1,
        },
    };
    <RsaSignatureExponentiation as Circuit<Bls12>>::synthesize(ckt, &mut ct).unwrap();
    println!("constraints: {}", ct.num_constraints());
}
