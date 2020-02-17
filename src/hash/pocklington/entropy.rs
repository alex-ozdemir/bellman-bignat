use sapling_crypto::bellman::pairing::ff::{Field, PrimeField, ScalarEngine};
use sapling_crypto::bellman::pairing::Engine;
use sapling_crypto::bellman::{ConstraintSystem, LinearCombination, SynthesisError};
use sapling_crypto::circuit::num::AllocatedNum;

use super::super::hashes::mimc;
use mp::bignat::BigNat;
use util::bit::{Bit, Bitvector};
use util::gadget::Gadget;

use std::default::Default;

#[derive(Debug)]
pub struct NatTemplate {
    pub random_bits: usize,
    pub leading_ones: usize,
    pub trailing: Padding,
}

impl NatTemplate {
    pub fn with_random_bits(count: usize) -> Self {
        Self {
            random_bits: count,
            leading_ones: 0,
            trailing: Padding::default(),
        }
    }

    pub fn with_leading_ones(mut self, count: usize) -> Self {
        self.leading_ones = count;
        self
    }

    pub fn with_trailing(mut self, bit: bool, count: usize) -> Self {
        self.trailing = Padding { bit, count };
        self
    }
}

#[derive(Debug)]
pub struct Padding {
    pub bit: bool,
    pub count: usize,
}

impl Default for Padding {
    fn default() -> Self {
        Self {
            bit: false,
            count: 0,
        }
    }
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
        let mut bits = vec![Bit::new_value::<CS>(true); template.leading_ones];
        for _ in 0..template.random_bits {
            bits.push(self.get_bit());
        }
        bits.extend(
            std::iter::repeat(Bit::new_value::<CS>(template.trailing.bit))
                .take(template.trailing.count),
        );
        bits.reverse();
        let mut r = BigNat::recompose(&Bitvector::from_bits(bits), limb_width);
        r.params.min_bits = if template.leading_ones > 0 {
            template.leading_ones + template.random_bits + template.trailing.count
        } else if template.trailing.bit {
            template.trailing.count
        } else {
            0
        };
        r
    }
}

pub mod helper {
    use super::NatTemplate;
    use rug::Integer;

    use sapling_crypto::bellman::pairing::ff::PrimeField;

    use hash::hashes::mimc;
    use util::convert::f_to_nat;

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
                bits.extend(n.to_digits::<bool>(rug::integer::Order::Lsf));
                let ex_len = (i + 1) * (F::CAPACITY as usize);
                bits.truncate(ex_len);
                bits.extend(std::iter::repeat(false).take(ex_len - bits.len()));
            }
            Self { bits }
        }
        pub fn get_bit(&mut self) -> bool {
            self.bits.pop().unwrap()
        }
        pub fn get_bits_as_nat(&mut self, template: NatTemplate) -> Integer {
            let mut acc = Integer::from(0);
            for _ in 0..template.leading_ones {
                acc = (acc << 1) + 1;
            }
            for _ in 0..template.random_bits {
                acc = (acc << 1)
                    | if self.get_bit() {
                        Integer::from(1)
                    } else {
                        Integer::from(0)
                    }
            }
            for _ in 0..template.trailing.count {
                acc = (acc << 1) + template.trailing.bit as u8;
            }
            acc
        }
    }
}
