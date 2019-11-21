# Bellman-BigNat

This is a Bellman library for multiprecision arithmetic and RSA accumulators
inside SNARKs.

## Contents

   * An implementation of multiprecision natural arithmetic based on the
      techniques of xJsnark, with additional features and optimizations.
   * A unified interface for a variety of hash functions.
      * Poseidon (from `sapling_crypto-ce`)
      * Pedersen (from `sapling_crypto-ce`)
      * Sha256 (from `sapling_crypto-ce`)
      * MiMC
   * A hash to provable primes, and associated checking machinery.
   * A division-intractable hash.
   * A hash-generic implementation of Merkle trees.
   * A hash-generic implementation of an RSA accumulator.

## Development

Development is ongoing.

Test can be run using `cargo`.

## Examples

   * `set_proof N_SWAPS` does setup for, writes a proof of, and then checks the
      proof of `n` swaps in an RSA accumulator.
   * `set_bench` is used for measuring the constraint costs of RSA and Merkle
      accumulators when performing swaps in a set. It does not actually
      synthesize any proofs.
   * `rollup_bench` is for measuring the constraint costs of a payment system
      backed by RSA and Merkle accumulators.

