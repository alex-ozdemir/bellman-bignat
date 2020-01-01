
/// Computes the optimal window size, k, for a windowed (Bauer) exponentiation with an n-bit
/// exponent.
pub fn optimal_k(n: usize) -> usize {
    for k in 1.. {
        let fk = k as f64;
        if (n as f64)
            < (fk * (fk + 1.0) * 2f64.powf(2.0 * fk)) / (2f64.powf(fk + 1.0) - fk - 2.0) + 1.0
        {
            return k;
        }
    }
    unreachable!()
}
