pub mod miller_rabin_prime;
pub mod pocklington;
pub mod rsa;
pub mod tree;
pub mod mimc;

use sapling_crypto::bellman::pairing::Engine;
use sapling_crypto::circuit::num::AllocatedNum;
use CResult;

pub struct MaybeHashed<E: Engine> {
    pub values: Vec<AllocatedNum<E>>,
    pub hash: Option<AllocatedNum<E>>,
}

impl<E: Engine> MaybeHashed<E> {
    pub fn new(values: Vec<AllocatedNum<E>>, hash: AllocatedNum<E>) -> Self {
        Self {
            values,
            hash: Some(hash),
        }
    }
    pub fn from_values(values: Vec<AllocatedNum<E>>) -> Self {
        Self {
            values,
            hash: None,
        }
    }
    pub fn get_hash<F: FnOnce(&[AllocatedNum<E>]) -> CResult<AllocatedNum<E>>>(&mut self, f: F) -> CResult<AllocatedNum<E>> {
        if self.hash.is_none() {
            self.hash = Some(f(&self.values)?);
        }
        Ok(self.hash.clone().unwrap())
    }
}

/// A representation of an integer domain to hash to
#[derive(Clone, Debug)]
pub struct HashDomain {
    pub n_bits: usize,
    pub n_trailing_ones: usize,
}

impl HashDomain {
    pub fn nonce_width(&self) -> usize {
        let n_rounds = -128f64 * 2f64.ln() / (1f64 - 2f64 / self.n_bits as f64).ln();
        let n_bits = (n_rounds.log2().ceil() + 0.1) as usize;
        n_bits
    }
}

pub mod helper {

    use num_bigint::BigUint;
    use num_traits::One;

    /// Given an integer, returns the integer with its low `k` bits.
    pub fn low_k_bits(n: &BigUint, k: usize) -> BigUint {
        n & ((BigUint::one() << k) - 1usize)
    }
}
