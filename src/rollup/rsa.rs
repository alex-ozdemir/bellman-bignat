
use rand::Rng;

use sapling_crypto::jubjub::{JubjubEngine, FixedGenerators, JubjubParams, PrimeOrder};
use sapling_crypto::bellman::{ConstraintSystem, Circuit};
use sapling_crypto::eddsa::{PublicKey, PrivateKey};
use sapling_crypto::circuit::ecc::EdwardsPoint;

use rollup::tx::{Action, SignedTx};
use rollup::tx::circuit::CircuitSignedTx;
use rollup::sig::allocate_point;
use hash::tree::Hasher;
use hash::tree::Pedersen;
use CResult;
use gadget::Gadget;

use std::collections::HashMap;
use std::rc::Rc;

#[derive(Derivative)]
#[derivative(Clone(bound=""))]
pub struct Account<E>
where
    E: JubjubEngine,
{
    pub id: PublicKey<E>,
    pub amt: usize,
    pub next_tx_no: usize,
}

#[derive(Derivative)]
#[derivative(Clone(bound=""))]
pub struct Accounts<E>
where
    E: JubjubEngine,
{
    map: HashMap<Vec<u8>, Account<E>>,
}

impl<E> Accounts<E>
where
    E: JubjubEngine,
{
    pub fn new() -> Accounts<E> {
        Self {
            map: HashMap::new(),
        }
    }

    pub fn insert(&mut self, a: Account<E>) {
        let mut key = Vec::new();
        a.id.write(&mut key).unwrap();
        assert!(self.map.insert(key, a).is_none());
    }
}

pub struct RollupBenchInputs<E>
where
    E: JubjubEngine,
{
    /// The transactions to do
    pub transactions: Vec<SignedTx<E>>,
    /// The initial account stat
    pub accounts: Accounts<E>,
}

impl<E> RollupBenchInputs<E>
where
    E: JubjubEngine,
{
    fn from_counts(n: usize, params: Rc<E::Params>) -> Self {
        let gens = FixedGenerators::SpendingKeyGenerator;
        let hasher = Pedersen::<E> {
            params: params.clone(),
        };
        let mut sks = Vec::new();
        let mut rng = rand::thread_rng();
        for _ in 0..n {
            sks.push(PrivateKey(rng.gen()));
        }
        let pks: Vec<_> = sks.iter().map(|k| PublicKey::from_private(k, gens, params.as_ref())).collect();
        let mut txs = Vec::new();
        for i in 0..n {
            let action = Action {
                dst: pks[(i + 1) % n].clone(),
                amt: (i + 1) as u64,
                tx_no: 0,
            };
            txs.push(action.sign(&mut rng, gens, params.as_ref(), &hasher, &sks[i]));
        }
        Self {
            transactions: txs,
            accounts: Accounts::new(),
        }
    }
}

pub struct RollupBenchParams<E>
where
    E: JubjubEngine,
{
    pub sig_params: Rc<E::Params>,
    pub sig_hasher: Pedersen<E>,
    pub gen: FixedGenerators,
    pub n_tx: usize,
}

pub struct RollupBench<E>
where
    E: JubjubEngine,
{
    pub input: Option<RollupBenchInputs<E>>,
    pub params: RollupBenchParams<E>,
}

impl<E> RollupBench<E>
where
    E: JubjubEngine,
{
    pub fn from_counts(n: usize, params: E::Params) -> Self {
        let params = Rc::new(params);
        Self {
            input: Some(RollupBenchInputs::from_counts(n, params.clone())),
            params: RollupBenchParams {
                sig_params: params.clone(),
                sig_hasher: Pedersen {
                    params: params.clone(),
                },
                gen: FixedGenerators::SpendingKeyGenerator,
                n_tx: n,
            },
        }
    }
}

impl<E> Circuit<E> for RollupBench<E>
where
    E: JubjubEngine,
{
    fn synthesize<CS: ConstraintSystem<E>>(self, cs: &mut CS) -> CResult<()> {
        let gen_value = self.params.sig_params.generator(FixedGenerators::SpendingKeyGenerator);
        let gen: EdwardsPoint<E> = allocate_point::<E, PrimeOrder, _>(
            cs.namespace(|| "gen"),
            Some(gen_value),
            &self.params.sig_params,
        )?;
        for tx_i in 0..self.params.n_tx {
            let mut cs = cs.namespace(|| format!("tx {}", tx_i));
            let signed_tx = CircuitSignedTx::alloc(
                cs.namespace(|| "alloc"),
                self.input.as_ref().map(|i| &i.transactions[tx_i]),
                (),
                &self.params.sig_params.clone(),
            )?;
            signed_tx.check_signature(
                cs.namespace(|| "check sig"),
                &self.params.sig_hasher,
                gen.clone(),
            )?;
        }
        Ok(())
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use test_helpers::*;

    use sapling_crypto::bellman::pairing::bn256::Bn256;
    use sapling_crypto::alt_babyjubjub::AltJubjubBn256;
    use hash::tree::Pedersen;

    circuit_tests! {
        rsa_rollup_0: (RollupBench::from_counts(0, AltJubjubBn256::new()), true),
        rsa_rollup_1: (RollupBench::from_counts(1, AltJubjubBn256::new()), true),
        rsa_rollup_10: (RollupBench::from_counts(10, AltJubjubBn256::new()), true),
    }
}
