pub mod miller_rabin_prime;
pub mod pocklington;
pub mod rsa;

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

