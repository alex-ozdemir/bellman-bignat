#![feature(hash_raw_entry)]
#![feature(test)]

extern crate bincode;
extern crate bitintr;
extern crate flate2;
extern crate fnv;
extern crate gmp_mpfr_sys;
extern crate rand;
extern crate rayon;
extern crate sapling_crypto;
extern crate test;
#[macro_use]
extern crate derivative;
extern crate rug;
extern crate serde;
extern crate sha2;

#[cfg(test)]
extern crate quickcheck;
#[cfg(test)]
#[macro_use(quickcheck)]
extern crate quickcheck_macros;

#[macro_use]
pub mod util;
pub mod group;
pub mod hash;
pub mod mp;
pub mod rollup;
pub mod set;
pub mod wesolowski;

use sapling_crypto::bellman::SynthesisError;

type CResult<T> = Result<T, SynthesisError>;

trait OptionExt<T> {
    fn grab(&self) -> Result<&T, SynthesisError>;
    fn grab_mut(&mut self) -> Result<&mut T, SynthesisError>;
}

impl<T> OptionExt<T> for Option<T> {
    fn grab(&self) -> Result<&T, SynthesisError> {
        self.as_ref().ok_or(SynthesisError::AssignmentMissing)
    }
    fn grab_mut(&mut self) -> Result<&mut T, SynthesisError> {
        self.as_mut().ok_or(SynthesisError::AssignmentMissing)
    }
}
