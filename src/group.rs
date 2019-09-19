use num_bigint::BigUint;
use num_traits::One;
use sapling_crypto::bellman::pairing::Engine;
use sapling_crypto::bellman::{ConstraintSystem, LinearCombination, SynthesisError};

use std::cmp::{min, PartialEq, Eq};
use std::fmt::{self, Formatter, Debug, Display};

use bignat::{BigNat, BigNatParams};
use bit::{Bit, Bitvector};
use exp::optimal_k;
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

#[derive(Clone, PartialEq, Eq)]
pub struct RsaGroup {
    pub g: BigUint,
    pub m: BigUint,
}

impl Debug for RsaGroup {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        f.debug_struct("RsaGroup")
            .field("g", &format_args!("{}", &self.g))
            .field("m", &format_args!("{}", &self.m))
            .finish()
    }
}

impl Display for RsaGroup {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        f.debug_struct("RsaGroup")
            .field("g", &format_args!("{}", &self.g))
            .field("m", &format_args!("{}", &self.m))
            .finish()
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

#[derive(Clone, PartialEq, Eq)]
pub struct RsaQuotientGroup {
    pub g: BigUint,
    pub m: BigUint,
}

impl Debug for RsaQuotientGroup {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        f.debug_struct("RsaQuotientGroup")
            .field("g", &format_args!("{}", &self.g))
            .field("m", &format_args!("{}", &self.m))
            .finish()
    }
}

impl Display for RsaQuotientGroup {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        f.debug_struct("RsaQuotientGroup")
            .field("g", &format_args!("{}", &self.g))
            .field("m", &format_args!("{}", &self.m))
            .finish()
    }
}

impl SemiGroup for RsaQuotientGroup {
    type Elem = BigUint;

    fn op(&self, a: &BigUint, b: &BigUint) -> BigUint {
        let x = a * b % &self.m;
        let y = &self.m - &x;
        min(x, y)
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
    fn partial_op<CS: ConstraintSystem<Self::E>>(
        &self,
        cs: CS,
        a: &Self::Elem,
        b: &Self::Elem,
    ) -> Result<Self::Elem, SynthesisError>;
    fn generator(&self) -> Self::Elem;
    fn identity(&self) -> Self::Elem;
    fn group(&self) -> Option<&Self::Group>;
    fn elem_params(p: &<Self as Gadget>::Params) -> <Self::Elem as Gadget>::Params;
    fn bauer_power_bin_rev_helper<'a, CS: ConstraintSystem<Self::E>>(
        &self,
        mut cs: CS,
        base_powers: &[Self::Elem],
        k: usize,
        mut exp_chunks: std::slice::Chunks<'a, Bit<Self::E>>,
    ) -> Result<Self::Elem, SynthesisError> {
        if let Some(chunk) = exp_chunks.next_back() {
            let chunk_len = chunk.len();

            if exp_chunks.len() > 0 {
                let mut acc = self.bauer_power_bin_rev_helper(cs.namespace(|| "rec"), base_powers, k, exp_chunks)?;
                // Square once, for each bit in the chunk
                for j in 0..chunk_len {
                    acc = self.partial_op(cs.namespace(|| format!("square {}", j)), &acc, &acc)?;
                }
                // Select the correct base power
                let base_power = Gadget::mux_tree(cs.namespace(|| "select"), chunk.into_iter(), &base_powers[..(1<<chunk_len)])?;
                self.partial_op(cs.namespace(|| "prod"), &acc, &base_power)
            } else {
                Gadget::mux_tree(cs.namespace(|| "select"), chunk.into_iter(), &base_powers[..(1<<chunk_len)])
            }
        } else {
            Ok(self.identity())
        }
    }
    fn bauer_power_bin_rev<CS: ConstraintSystem<Self::E>>(
        &self,
        mut cs: CS,
        base: &Self::Elem,
        exp: Bitvector<Self::E>,
    ) -> Result<Self::Elem, SynthesisError> {
        // https://en.wikipedia.org/wiki/Exponentiation_by_squaring#2k-ary_method
        let k = optimal_k(exp.bits.len());
        let base_powers = {
            let mut base_powers = vec![self.identity(), base.clone()];
            for i in 2..(1<<k) {
                base_powers.push(self.partial_op(cs.namespace(|| format!("base {}", i)), base_powers.last().unwrap(), base)?);
            }
            base_powers
        };
        self.bauer_power_bin_rev_helper(cs.namespace(|| "helper"), &base_powers, k, exp.into_bits().chunks(k))
    }
    fn power<CS: ConstraintSystem<Self::E>>(
        &self,
        mut cs: CS,
        b: &Self::Elem,
        e: &BigNat<Self::E>,
    ) -> Result<Self::Elem, SynthesisError> {
        let exp_bin_rev = e.decompose(cs.namespace(|| "exp decomp"))?.reversed();
        self.bauer_power_bin_rev(cs.namespace(|| "binary exp"), &b, exp_bin_rev)
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

impl<E: Engine> PartialEq for CircuitRsaGroup<E> {
    fn eq(&self, other: &Self) -> bool {
        self.g == other.g
            && self.m == other.m
            && self.id == other.id
            && self.value == other.value
            && self.params == other.params
    }
}
impl<E: Engine> Eq for CircuitRsaGroup<E> {}

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
        let mut m = <BigNat<E> as Gadget>::alloc(
            cs.namespace(|| "m"),
            value.as_ref().map(|v| &v.m),
            (),
            &BigNatParams::new(params.limb_width, params.n_limbs),
        )?;
        m.enforce_full_bits(cs.namespace(|| "m is full"))?;

        let id = BigNat::identity::<CS>(params.limb_width);
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
    fn partial_op<CS: ConstraintSystem<E>>(
        &self,
        cs: CS,
        a: &BigNat<E>,
        b: &BigNat<E>,
    ) -> Result<BigNat<E>, SynthesisError> {
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

#[derive(Clone)]
pub struct CircuitRsaQuotientGroup<E: Engine> {
    pub g: BigNat<E>,
    pub m: BigNat<E>,
    pub id: BigNat<E>,
    pub value: Option<RsaQuotientGroup>,
    pub params: CircuitRsaGroupParams,
}

impl<E: Engine> PartialEq for CircuitRsaQuotientGroup<E> {
    fn eq(&self, other: &Self) -> bool {
        self.g == other.g
            && self.m == other.m
            && self.id == other.id
            && self.value == other.value
            && self.params == other.params
    }
}

impl<E: Engine> CircuitRsaQuotientGroup<E> {
}

impl<E: Engine> Eq for CircuitRsaQuotientGroup<E> {}

impl<E: Engine> Gadget for CircuitRsaQuotientGroup<E> {
    type E = E;
    type Value = RsaQuotientGroup;
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
        let mut m = <BigNat<E> as Gadget>::alloc(
            cs.namespace(|| "m"),
            value.as_ref().map(|v| &v.m),
            (),
            &BigNatParams::new(params.limb_width, params.n_limbs),
        )?;
        m.enforce_full_bits(cs.namespace(|| "m is full"))?;

        let id = BigNat::identity::<CS>(params.limb_width);
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

impl<E: Engine> CircuitSemiGroup for CircuitRsaQuotientGroup<E> {
    type Elem = BigNat<E>;
    type Group = RsaQuotientGroup;
    fn op<CS: ConstraintSystem<E>>(
        &self,
        mut cs: CS,
        a: &BigNat<E>,
        b: &BigNat<E>,
    ) -> Result<Self::Elem, SynthesisError> {
        let x = self.partial_op(cs.namespace(|| "mult"), a, b)?;
        let y = self.m.sub(cs.namespace(|| "sub"), &x)?;
        y.decompose(cs.namespace(|| "y decomp check"))?;
        x.min(cs.namespace(|| "min"), &y)
    }
    fn partial_op<CS: ConstraintSystem<E>>(
        &self,
        cs: CS,
        a: &BigNat<E>,
        b: &BigNat<E>,
    ) -> Result<BigNat<E>, SynthesisError> {
        a.mult_mod(cs, b, &self.m).map(|(_, r)| r)
    }
    fn power<CS: ConstraintSystem<Self::E>>(
        &self,
        mut cs: CS,
        b: &Self::Elem,
        e: &BigNat<Self::E>,
    ) -> Result<Self::Elem, SynthesisError> {
        let exp_bin_rev = e.decompose(cs.namespace(|| "exp decomp"))?.reversed();
        let x = self.bauer_power_bin_rev(cs.namespace(|| "binary exp"), &b, exp_bin_rev)?;
        let y = self.m.sub(cs.namespace(|| "sub"), &x)?;
        y.decompose(cs.namespace(|| "y decomp check"))?;
        x.min(cs.namespace(|| "min"), &y)
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

#[cfg(test)]
mod test {
    use super::*;
    use test_helpers::*;
    use OptionExt;
    use std::str::FromStr;

    #[derive(Debug)]
    pub struct PowerInputs<'a> {
        pub g: &'a str,
        pub m: &'a str,
        pub b: &'a str,
        pub e: &'a str,
        pub res: &'a str,
    }

    pub struct PowerParams {
        pub limb_width: usize,
        pub n_limbs_b: usize,
        pub n_limbs_e: usize,
    }

    pub struct Power<'a> {
        inputs: Option<PowerInputs<'a>>,
        params: PowerParams,
    }

    impl<'a, E: Engine> Circuit<E> for Power<'a> {
        fn synthesize<CS: ConstraintSystem<E>>(self, cs: &mut CS) -> Result<(), SynthesisError> {
            let ins = self.inputs.grab()?;
            let group = CircuitRsaGroup::alloc(
                cs.namespace(|| "group"),
                Some(
                    &RsaGroup {
                        g: BigUint::from_str(ins.g).unwrap(),
                        m: BigUint::from_str(ins.m).unwrap(),
                    }
                ),
                (),
                &CircuitRsaGroupParams {
                    limb_width: self.params.limb_width,
                    n_limbs: self.params.n_limbs_b,
                },
            )?;
            let b = BigNat::alloc_from_nat(
                cs.namespace(|| "b"),
                || Ok(BigUint::from_str(self.inputs.grab()?.b).unwrap()),
                self.params.limb_width,
                self.params.n_limbs_b,
            )?;
            let e = BigNat::alloc_from_nat(
                cs.namespace(|| "e"),
                || Ok(BigUint::from_str(self.inputs.grab()?.e).unwrap()),
                self.params.limb_width,
                self.params.n_limbs_e,
            )?;
            let res = BigNat::alloc_from_nat(
                cs.namespace(|| "res"),
                || Ok(BigUint::from_str(self.inputs.grab()?.res).unwrap()),
                self.params.limb_width,
                self.params.n_limbs_b,
            )?;
            let actual = group.power(cs.namespace(|| "pow"), &b, &e)?;
            actual.equal(cs.namespace(|| "check"), &res)?;
            Ok(())
        }
    }

    circuit_tests! {
        power_1_1: (
            Power {
                inputs: Some(PowerInputs {
                    g: "2",
                    m: "241",
                    b: "1",
                    e: "1",
                    res: "1",
                }),
                params: PowerParams {
                    limb_width: 4,
                    n_limbs_b: 2,
                    n_limbs_e: 12,
                }
            },
            true,
        ),
        power_1_0: (
            Power {
                inputs: Some(PowerInputs {
                    g: "2",
                    m: "241",
                    b: "1",
                    e: "0",
                    res: "1",
                }),
                params: PowerParams {
                    limb_width: 4,
                    n_limbs_b: 2,
                    n_limbs_e: 12,
                }
            },
            true,
        ),

        power_5_12351: (
            Power {
                inputs: Some(PowerInputs {
                    g: "2",
                    m: "241",
                    b: "5",
                    e: "12351",
                    res: "162",
                }),
                params: PowerParams {
                    limb_width: 4,
                    n_limbs_b: 2,
                    n_limbs_e: 12,
                }
            },
            true,
        ),
        power_512b_128b: (
            Power {
                inputs: Some(PowerInputs {
                    g: "2",
                    m: "11834783464130424096695514462778870280264989938857328737807205623069291535525952722847913694296392927890261736769191982212777933726583565708193466779811767",
                    b: "5",
                    e: "1",
                    res: "5",
                }),
                params: PowerParams {
                    limb_width: 32,
                    n_limbs_b: 16,
                    n_limbs_e: 4,
                }
            },
            true,
        ),
    }

    #[derive(Debug)]
    pub struct RsaQuotientOpInputs<'a> {
        pub m: &'a str,
        pub a: &'a str,
        pub b: &'a str,
    }

    pub struct RsaQuotientOpParams {
        pub limb_width: usize,
        pub n_limbs: usize,
    }

    pub struct RsaQuotientOp<'a> {
        inputs: Option<RsaQuotientOpInputs<'a>>,
        params: RsaQuotientOpParams,
    }

    impl<'a, E: Engine> Circuit<E> for RsaQuotientOp<'a> {
        fn synthesize<CS: ConstraintSystem<E>>(self, cs: &mut CS) -> Result<(), SynthesisError> {
            let ins = self.inputs.grab()?;
            let group = CircuitRsaQuotientGroup::alloc(
                cs.namespace(|| "group"),
                Some(
                    &RsaQuotientGroup {
                        g: BigUint::from_str("2").unwrap(),
                        m: BigUint::from_str(ins.m).unwrap(),
                    }
                ),
                (),
                &CircuitRsaGroupParams {
                    limb_width: self.params.limb_width,
                    n_limbs: self.params.n_limbs,
                },
            )?;
            let b = BigNat::alloc_from_nat(
                cs.namespace(|| "b"),
                || Ok(BigUint::from_str(self.inputs.grab()?.b).unwrap()),
                self.params.limb_width,
                self.params.n_limbs,
            )?;
            let a = BigNat::alloc_from_nat(
                cs.namespace(|| "a"),
                || Ok(BigUint::from_str(self.inputs.grab()?.a).unwrap()),
                self.params.limb_width,
                self.params.n_limbs,
            )?;
            let res = BigNat::alloc_from_nat(
                cs.namespace(|| "res"),
                || Ok(group.group().grab()?.op(a.value.grab()?, b.value.grab()?)),
                self.params.limb_width,
                self.params.n_limbs,
            )?;
            let actual = group.op(cs.namespace(|| "pow"), &a, &b)?;
            actual.equal(cs.namespace(|| "check"), &res)?;
            Ok(())
        }
    }

    circuit_tests! {
        quotient_op_1_1: (
            RsaQuotientOp {
                inputs: Some(RsaQuotientOpInputs {
                    m: "241",
                    a: "1",
                    b: "1",
                }),
                params: RsaQuotientOpParams {
                    limb_width: 4,
                    n_limbs: 2,
                }
            },
            true,
        ),
        quotient_op_15_27: (
            RsaQuotientOp {
                inputs: Some(RsaQuotientOpInputs {
                    m: "241",
                    a: "15",
                    b: "27",
                }),
                params: RsaQuotientOpParams {
                    limb_width: 4,
                    n_limbs: 2,
                }
            },
            true,
        ),
    }

    #[derive(Debug)]
    pub struct QuotientPowerInputs<'a> {
        pub g: &'a str,
        pub m: &'a str,
        pub b: &'a str,
        pub e: &'a str,
        pub res: &'a str,
    }

    pub struct QuotientPowerParams {
        pub limb_width: usize,
        pub n_limbs_b: usize,
        pub n_limbs_e: usize,
    }

    pub struct QuotientPower<'a> {
        inputs: Option<QuotientPowerInputs<'a>>,
        params: QuotientPowerParams,
    }

    impl<'a, E: Engine> Circuit<E> for QuotientPower<'a> {
        fn synthesize<CS: ConstraintSystem<E>>(self, cs: &mut CS) -> Result<(), SynthesisError> {
            let ins = self.inputs.grab()?;
            let group = CircuitRsaQuotientGroup::alloc(
                cs.namespace(|| "group"),
                Some(
                    &RsaQuotientGroup {
                        g: BigUint::from_str(ins.g).unwrap(),
                        m: BigUint::from_str(ins.m).unwrap(),
                    }
                ),
                (),
                &CircuitRsaGroupParams {
                    limb_width: self.params.limb_width,
                    n_limbs: self.params.n_limbs_b,
                },
            )?;
            let b = BigNat::alloc_from_nat(
                cs.namespace(|| "b"),
                || Ok(BigUint::from_str(self.inputs.grab()?.b).unwrap()),
                self.params.limb_width,
                self.params.n_limbs_b,
            )?;
            let e = BigNat::alloc_from_nat(
                cs.namespace(|| "e"),
                || Ok(BigUint::from_str(self.inputs.grab()?.e).unwrap()),
                self.params.limb_width,
                self.params.n_limbs_e,
            )?;
            let res = BigNat::alloc_from_nat(
                cs.namespace(|| "res"),
                || Ok(BigUint::from_str(self.inputs.grab()?.res).unwrap()),
                self.params.limb_width,
                self.params.n_limbs_b,
            )?;
            let actual = group.power(cs.namespace(|| "pow"), &b, &e)?;
            actual.equal(cs.namespace(|| "check"), &res)?;
            Ok(())
        }
    }

    circuit_tests! {
        quotient_power_1_1: (
            QuotientPower {
                inputs: Some(QuotientPowerInputs {
                    g: "2",
                    m: "241",
                    b: "1",
                    e: "1",
                    res: "1",
                }),
                params: QuotientPowerParams {
                    limb_width: 4,
                    n_limbs_b: 2,
                    n_limbs_e: 12,
                }
            },
            true,
        ),
        quotient_power_1_0: (
            QuotientPower {
                inputs: Some(QuotientPowerInputs {
                    g: "2",
                    m: "241",
                    b: "1",
                    e: "0",
                    res: "1",
                }),
                params: QuotientPowerParams {
                    limb_width: 4,
                    n_limbs_b: 2,
                    n_limbs_e: 12,
                }
            },
            true,
        ),

        quotient_power_5_12351: (
            QuotientPower {
                inputs: Some(QuotientPowerInputs {
                    g: "2",
                    m: "241",
                    b: "5",
                    e: "12351",
                    res: "79",
                }),
                params: QuotientPowerParams {
                    limb_width: 4,
                    n_limbs_b: 2,
                    n_limbs_e: 12,
                }
            },
            true,
        ),
        quotient_power_512b_128b: (
            QuotientPower {
                inputs: Some(QuotientPowerInputs {
                    g: "2",
                    m: "11834783464130424096695514462778870280264989938857328737807205623069291535525952722847913694296392927890261736769191982212777933726583565708193466779811767",
                    b: "5",
                    e: "1",
                    res: "5",
                }),
                params: QuotientPowerParams {
                    limb_width: 32,
                    n_limbs_b: 16,
                    n_limbs_e: 4,
                }
            },
            true,
        ),
        quotient_power_2048b_128b: (
            QuotientPower {
                inputs: Some(QuotientPowerInputs {
                    g: "2",
                    m: "22747784372797411031619218405252916426354121290914480307874578163525619541112683924343899933014404205047179650229236510963274298270596407894802435755873412801151123349920293891256387516575679268349468635787138056777772304133679209920498899381037779099894464877207451756681230792511889538129801692603270091191400586328425648063191513137075190895387240401681110314601347581109790977516732007935069514700102058033826025978640567291712386409661705262833874766697139640252582245921204119623927250097747435414874229566445355653125751434614915009077031929051847007645668425735284036921169883199278456158026590858343256375547",
                    b: "1",
                    e: "2",
                    res: "1",
                }),
                params: QuotientPowerParams {
                    limb_width: 32,
                    n_limbs_b: 64,
                    n_limbs_e: 4,
                }
            },
            true,
        ),
        power_2048b_128b: (
            Power {
                inputs: Some(PowerInputs {
                    g: "2",
                    m: "22747784372797411031619218405252916426354121290914480307874578163525619541112683924343899933014404205047179650229236510963274298270596407894802435755873412801151123349920293891256387516575679268349468635787138056777772304133679209920498899381037779099894464877207451756681230792511889538129801692603270091191400586328425648063191513137075190895387240401681110314601347581109790977516732007935069514700102058033826025978640567291712386409661705262833874766697139640252582245921204119623927250097747435414874229566445355653125751434614915009077031929051847007645668425735284036921169883199278456158026590858343256375547",
                    b: "1",
                    e: "2",
                    res: "1",
                }),
                params: PowerParams {
                    limb_width: 32,
                    n_limbs_b: 64,
                    n_limbs_e: 4,
                }
            },
            true,
        ),
    }

}


