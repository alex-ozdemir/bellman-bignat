use num_bigint::BigUint;
use num_traits::One;
use sapling_crypto::bellman::pairing::Engine;
use sapling_crypto::bellman::{ConstraintSystem, LinearCombination, SynthesisError};

use std::cmp::Eq;
use std::fmt::{Debug, Display};

use bignat::{BigNat, BigNatParams};
use bit::{Bit, Bitvector};
use gadget::Gadget;

pub trait SemiGroup: Clone + Eq + Debug + Display {
    type Elem: Clone + Debug + Ord + Display;
    fn op(&self, a: &Self::Elem, b: &Self::Elem) -> Self::Elem;
    fn identity(&self) -> Self::Elem;
    fn generator(&self) -> Self::Elem;
    fn power(&self, b: &Self::Elem, e: &BigUint) -> Self::Elem {
        let mut acc = self.identity();
        let bits = e.to_str_radix(2);
        for bit in bits.bytes() {
            match bit {
                b'0' => {
                    acc = self.op(&acc, &acc);
                }
                b'1' => {
                    acc = self.op(&self.op(&acc, &acc), &b);
                }
                _ => unreachable!(),
            }
        }
        acc
    }
}

// TODO (aozdemir) mod out by the <-1> subgroup.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RsaGroup {
    pub g: BigUint,
    pub m: BigUint,
}

impl Display for RsaGroup {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "RsaGroup(g = {}, m = {})", self.g, self.m)
    }
}

impl SemiGroup for RsaGroup {
    type Elem = BigUint;

    fn op(&self, a: &BigUint, b: &BigUint) -> BigUint {
        a * b % &self.m
    }

    fn identity(&self) -> BigUint {
        BigUint::one()
    }

    fn generator(&self) -> BigUint {
        self.g.clone()
    }
}

pub trait CircuitSemiGroup: Gadget<Access=()> + Eq {
    type Elem: Clone + Gadget<E = Self::E> + Eq + Display;
    type Group: SemiGroup;
    fn op<CS: ConstraintSystem<Self::E>>(
        &self,
        cs: CS,
        a: &Self::Elem,
        b: &Self::Elem,
    ) -> Result<Self::Elem, SynthesisError>;
    fn generator(&self) -> Self::Elem;
    fn identity(&self) -> Self::Elem;
    fn group(&self) -> Option<&Self::Group>;
    fn elem_params(p: &<Self as Gadget>::Params) -> <Self::Elem as Gadget>::Params;
    fn power_bin_rev<CS: ConstraintSystem<Self::E>>(
        &self,
        mut cs: CS,
        base: &Self::Elem,
        mut exp: Bitvector<Self::E>,
    ) -> Result<Self::Elem, SynthesisError> {
        if exp.bits.len() == 0 {
            Ok(self.identity())
        } else {
            let square = self.op(cs.namespace(|| "square"), &base, &base)?;
            let select_bit = Bit {
                // Unwrap is safe b/c of `n_bits` check
                value: exp.values.as_mut().map(|vs| vs.pop().unwrap()),
                bit: exp.bits.pop().unwrap(),
            };
            let rec = self.power_bin_rev(cs.namespace(|| "rec"), &square, exp)?;
            let prod = self.op(cs.namespace(|| "prod"), &rec, &base)?;
            <Self::Elem as Gadget>::mux(cs.namespace(|| "mux"), &select_bit, &rec, &prod)
        }
    }
    fn power<CS: ConstraintSystem<Self::E>>(
        &self,
        mut cs: CS,
        b: &Self::Elem,
        e: &BigNat<Self::E>,
    ) -> Result<Self::Elem, SynthesisError> {
        let exp_bin_rev = e.decompose(cs.namespace(|| "exp decomp"))?.reversed();
        self.power_bin_rev(cs.namespace(|| "binary exp"), &b, exp_bin_rev)
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CircuitRsaGroupParams {
    pub limb_width: usize,
    pub n_limbs: usize,
}

#[derive(Clone)]
pub struct CircuitRsaGroup<E: Engine> {
    pub g: BigNat<E>,
    pub m: BigNat<E>,
    pub id: BigNat<E>,
    pub value: Option<RsaGroup>,
    pub params: CircuitRsaGroupParams,
}

impl<E: Engine> std::cmp::PartialEq for CircuitRsaGroup<E> {
    fn eq(&self, other: &Self) -> bool {
        self.g == other.g
            && self.m == other.m
            && self.id == other.id
            && self.value == other.value
            && self.params == other.params
    }
}
impl<E: Engine> std::cmp::Eq for CircuitRsaGroup<E> {}

impl<E: Engine> Gadget for CircuitRsaGroup<E> {
    type E = E;
    type Value = RsaGroup;
    type Params = CircuitRsaGroupParams;
    type Access = ();
    fn alloc<CS: ConstraintSystem<E>>(
        mut cs: CS,
        value: Option<&Self::Value>,
        _access: (),
        params: &Self::Params,
    ) -> Result<Self, SynthesisError> {
        let value = value.cloned();
        let g = <BigNat<E> as Gadget>::alloc(
            cs.namespace(|| "g"),
            value.as_ref().map(|v| &v.g),
            (),
            &BigNatParams::new(params.limb_width, params.n_limbs),
        )?;
        let m = <BigNat<E> as Gadget>::alloc(
            cs.namespace(|| "m"),
            value.as_ref().map(|v| &v.m),
            (),
            &BigNatParams::new(params.limb_width, params.n_limbs),
        )?;
        let one = BigUint::one();
        let id = <BigNat<E> as Gadget>::alloc(
            cs.namespace(|| "id"),
            value.as_ref().map(|_| &one),
            (),
            &BigNatParams::new(params.limb_width, params.n_limbs),
        )?;
        Ok(Self {
            g,
            m,
            id,
            value,
            params: params.clone(),
        })
    }
    fn wires(&self) -> Vec<LinearCombination<E>> {
        let mut wires = self.g.wires();
        wires.extend(self.m.wires());
        wires
    }
    fn wire_values(&self) -> Option<Vec<E::Fr>> {
        let mut vs = self.g.wire_values();
        vs.as_mut()
            .map(|vs| self.m.wire_values().map(|vs2| vs.extend(vs2)));
        vs
    }
    fn value(&self) -> Option<&Self::Value> {
        self.value.as_ref()
    }
    fn params(&self) -> &Self::Params {
        &self.params
    }
    fn access(&self) -> &() {
        &()
    }
}

impl<E: Engine> CircuitSemiGroup for CircuitRsaGroup<E> {
    type Elem = BigNat<E>;
    type Group = RsaGroup;
    fn op<CS: ConstraintSystem<E>>(
        &self,
        cs: CS,
        a: &BigNat<E>,
        b: &BigNat<E>,
    ) -> Result<Self::Elem, SynthesisError> {
        a.mult_mod(cs, b, &self.m).map(|(_, r)| r)
    }
    fn elem_params(p: &<Self as Gadget>::Params) -> <Self::Elem as Gadget>::Params {
        BigNatParams::new(p.limb_width, p.n_limbs)
    }
    fn group(&self) -> Option<&Self::Group> {
        self.value.as_ref()
    }
    fn generator(&self) -> Self::Elem {
        self.g.clone()
    }
    fn identity(&self) -> Self::Elem {
        self.id.clone()
    }
}
