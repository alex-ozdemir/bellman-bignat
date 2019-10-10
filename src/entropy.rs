use sapling_crypto::bellman::pairing::ff::{Field, PrimeField, ScalarEngine};
use sapling_crypto::bellman::pairing::Engine;
use sapling_crypto::bellman::{ConstraintSystem, LinearCombination, SynthesisError};
use sapling_crypto::circuit::num::AllocatedNum;

use bignat::BigNat;
use bit::{Bit, Bitvector};
use hash::mimc;

use gadget::Gadget;

#[derive(Debug)]
pub struct NatTemplate {
    pub random_bits: usize,
    pub leading_ones: usize,
    pub trailing_ones: usize,
}

#[derive(Clone)]
pub struct EntropySource<E: Engine> {
    base_hash: AllocatedNum<E>,
    bits: Bitvector<E>,
    entropy: usize,
}

impl<E: Engine> Gadget for EntropySource<E> {
    type E = E;
    type Value = ();
    type Access = AllocatedNum<E>;
    type Params = usize;

    fn wires(&self) -> Vec<LinearCombination<Self::E>> {
        self.bits.bits.clone()
    }
    fn wire_values(&self) -> Option<Vec<<Self::E as ScalarEngine>::Fr>> {
        self.bits.values.as_ref().map(|vs| {
            vs.iter()
                .map(|b| if *b { E::Fr::one() } else { E::Fr::zero() })
                .collect()
        })
    }
    fn value(&self) -> Option<&Self::Value> {
        Some(&())
    }
    fn access(&self) -> &Self::Access {
        &self.base_hash
    }
    fn params(&self) -> &Self::Params {
        &self.entropy
    }

    fn alloc<CS: ConstraintSystem<Self::E>>(
        mut cs: CS,
        _: Option<&Self::Value>,
        access: Self::Access,
        params: &Self::Params,
    ) -> Result<Self, SynthesisError> {
        let bits_needed = *params;
        let elems_needed = (bits_needed - 1) / E::Fr::CAPACITY as usize + 1;
        let mut elems: Vec<AllocatedNum<E>> = vec![access.clone()];
        while elems.len() < elems_needed {
            elems.push(mimc::permutation(
                cs.namespace(|| format!("hash {}", elems.len())),
                elems.last().unwrap().clone(),
            )?);
        }
        let mut bits = Vec::new();
        for (i, hash) in elems.into_iter().enumerate() {
            let mut h_bits = hash.into_bits_le_strict(cs.namespace(|| format!("decomp {}", i)))?;
            h_bits.truncate(E::Fr::CAPACITY as usize);
            bits.extend(h_bits.into_iter().map(|b| Bit::<E>::from_sapling::<CS>(b)));
        }
        Ok(EntropySource {
            bits: Bitvector::from_bits(bits),
            base_hash: access,
            entropy: bits_needed,
        })
    }
}

impl<E: Engine> EntropySource<E> {
    pub fn get_bit(&mut self) -> Bit<E> {
        self.bits.pop().unwrap()
    }
    pub fn get_bits_as_nat<CS: ConstraintSystem<E>>(
        &mut self,
        template: NatTemplate,
        limb_width: usize,
    ) -> BigNat<E> {
        let mut bits = vec![Bit::new_true::<CS>(); template.leading_ones];
        for _ in 0..template.random_bits {
            bits.push(self.get_bit());
        }
        for _ in 0..template.trailing_ones {
            bits.push(Bit::new_true::<CS>());
        }
        bits.reverse();
        BigNat::recompose(&Bitvector::from_bits(bits), limb_width)
    }
}

pub mod helper {
    use super::NatTemplate;
    use num_bigint::BigUint;
    use num_traits::{One, Zero};

    use sapling_crypto::bellman::pairing::ff::PrimeField;

    use f_to_nat;
    use hash::mimc;

    pub struct EntropySource {
        bits: Vec<bool>,
    }

    impl EntropySource {
        pub fn new<F: PrimeField>(hash: F, bits_needed: usize) -> Self {
            let elems_needed = (bits_needed - 1) / F::CAPACITY as usize + 1;
            let mut elems = vec![hash];
            while elems.len() < elems_needed {
                elems.push(mimc::helper::permutation(elems.last().unwrap().clone()));
            }
            let mut bits = Vec::new();
            for (i, hash) in elems.into_iter().enumerate() {
                let n = f_to_nat(&hash);
                bits.extend(
                    n.to_bytes_le()
                        .into_iter()
                        .flat_map(|byte| (0..8).map(move |i| (byte >> i) & 1 > 0)),
                );
                let ex_len = (i + 1) * (F::CAPACITY as usize);
                bits.truncate(ex_len);
                bits.extend(std::iter::repeat(false).take(ex_len - bits.len()));
            }
            Self { bits }
        }
        pub fn get_bit(&mut self) -> bool {
            self.bits.pop().unwrap()
        }
        pub fn get_bits_as_nat(&mut self, template: NatTemplate) -> BigUint {
            let mut acc = BigUint::zero();
            for _ in 0..template.leading_ones {
                acc = (acc << 1) + 1usize;
            }
            for _ in 0..template.random_bits {
                acc = (acc << 1)
                    | if self.get_bit() {
                        BigUint::one()
                    } else {
                        BigUint::zero()
                    }
            }
            for _ in 0..template.trailing_ones {
                acc = (acc << 1) + 1usize;
            }
            acc
        }
    }
}
