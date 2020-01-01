use rand::Rng;

use sapling_crypto::bellman::{Circuit, ConstraintSystem};
use sapling_crypto::circuit::ecc::EdwardsPoint;
use sapling_crypto::circuit::num::AllocatedNum;
use sapling_crypto::eddsa::{PrivateKey, PublicKey};
use sapling_crypto::jubjub::edwards::Point;
use sapling_crypto::jubjub::{FixedGenerators, JubjubEngine, JubjubParams, PrimeOrder};

use hash;
use hash::circuit::CircuitHasher;
use hash::hashes::Pedersen;
use hash::Hasher;
use rollup::sig::allocate_point;
use rollup::tx::circuit::{CircuitAccount, CircuitSignedTx};
use rollup::tx::{Account, Action, SignedTx, Tx, TxAccountChanges};
use set::merkle::{MerkleCircuitSet, MerkleSet};
use set::{CircuitGenSet, GenSet};
use util::convert::usize_to_f;
use util::gadget::Gadget;
use CResult;
use OptionExt;

use std::collections::HashMap;
use std::rc::Rc;

#[derive(Derivative)]
#[derivative(Clone(bound = ""))]
pub struct Accounts<E, H>
where
    E: JubjubEngine,
    H: Hasher,
{
    map: HashMap<Vec<u8>, Account<E>>,
    set: MerkleSet<H>,
}

impl<E, H> Accounts<E, H>
where
    E: JubjubEngine,
    H: Hasher<F = E::Fr>,
{
    pub fn new(s: &MerkleParams<H>, list_of_accounts: Vec<Account<E>>) -> Self {
        let list: Vec<Vec<E::Fr>> = list_of_accounts.iter().map(Account::as_elems).collect();
        Self {
            map: HashMap::new(),
            set: MerkleSet::new_with(s.hasher.clone(), s.depth, list.iter().map(Vec::as_slice)),
        }
    }

    pub fn swap(&mut self, a: Account<E>, b: Account<E>) {
        let mut key = Vec::new();
        a.id.write(&mut key).unwrap();
        self.set.swap(&a.as_elems(), b.as_elems());
    }

    pub fn get(&self, k: &PublicKey<E>) -> Option<&Account<E>> {
        let mut key = Vec::new();
        k.write(&mut key).unwrap();
        self.map.get(&key)
    }

    /// Applies this transaction to the accounts:
    ///    * mutating the state and
    ///    * returning the changes made
    pub fn apply_tx(&mut self, t: &Tx<E>) -> Option<TxAccountChanges<E>> {
        let dst_init = self.get(&t.action.dst)?.clone();
        let src_init = self.get(&t.src)?.clone();
        let src_final = {
            let mut src = src_init.clone();
            if src.amt < t.action.amt || src.next_tx_no != t.action.tx_no {
                return None;
            }
            src.amt = src.amt.checked_sub(t.action.amt)?;
            src.next_tx_no = src.next_tx_no.checked_add(1)?;
            src
        };
        let dst_final = {
            let mut dst = dst_init.clone();
            dst.amt = dst.amt.checked_add(t.action.amt)?;
            dst
        };
        self.swap(src_init.clone(), src_final.clone());
        self.swap(dst_init.clone(), dst_final.clone());
        Some(TxAccountChanges {
            src_init,
            src_final,
            dst_init,
            dst_final,
        })
    }
}

pub fn public_key_value<E: JubjubEngine>(
    k: &EdwardsPoint<E>,
    p: &E::Params,
) -> Option<PublicKey<E>> {
    Some(PublicKey(Point::from_xy(
        k.get_x().get_value()?,
        k.get_y().get_value()?,
        p,
    )?))
}

pub fn allocate_account<E, H, CS>(
    mut cs: CS,
    accounts: Option<&Accounts<E, H>>,
    k: EdwardsPoint<E>,
    next_tx_no: Option<AllocatedNum<E>>,
    p: &<E as JubjubEngine>::Params,
) -> CResult<CircuitAccount<E>>
where
    E: JubjubEngine,
    H: CircuitHasher<E = E> + Hasher<F = E::Fr>,
    CS: ConstraintSystem<E>,
{
    let next_tx_no = if let Some(next_tx_no) = next_tx_no {
        next_tx_no
    } else {
        AllocatedNum::alloc(cs.namespace(|| "next_tx_no"), || {
            Ok(usize_to_f(
                accounts
                    .grab()?
                    .get(public_key_value(&k, p).grab()?)
                    .grab()?
                    .next_tx_no as usize,
            ))
        })?
    };
    let amt = AllocatedNum::alloc(cs.namespace(|| "amt"), || {
        Ok(usize_to_f(
            accounts
                .grab()?
                .get(public_key_value(&k, p).grab()?)
                .grab()?
                .amt as usize,
        ))
    })?;
    Ok(CircuitAccount {
        id: k,
        next_tx_no,
        amt,
    })
}

pub struct RollupBenchInputs<E, H>
where
    E: JubjubEngine,
    H: Hasher,
{
    /// The transactions to do
    pub transactions: Vec<SignedTx<E>>,
    /// The initial account state
    pub accounts: Accounts<E, H>,
}

impl<E, H> RollupBenchInputs<E, H>
where
    E: JubjubEngine,
    H: Hasher<F = E::Fr>,
{
    /// Creates a benchmark where `t` coins are exchanged in a pool of size `c`.
    pub fn from_counts(c: usize, t: usize, p: &RollupBenchParams<E, H>) -> Self {
        let gens = FixedGenerators::SpendingKeyGenerator;
        let hasher = Pedersen::<E> {
            params: p.jj_params.clone(),
        };
        let mut sks = Vec::new();
        let mut rng = rand::thread_rng();
        for _ in 0..c {
            sks.push(PrivateKey(rng.gen()));
        }
        let pks: Vec<_> = sks
            .iter()
            .map(|k| PublicKey::from_private(k, gens, p.jj_params.as_ref()))
            .collect();
        let list_of_accounts = (0..c)
            .map(|i| Account {
                id: pks[i].clone(),
                amt: if i == 0 { 1 } else { 0 },
                next_tx_no: 0,
            })
            .collect::<Vec<_>>();
        let accounts = Accounts::new(&p.set_params, list_of_accounts);
        let mut transactions = Vec::new();
        for i in 0..t {
            let action = Action {
                dst: pks[(i + 1) % c].clone(),
                amt: 1,
                tx_no: (i / c) as u64,
            };
            transactions.push(action.sign(
                &mut rng,
                gens,
                p.jj_params.as_ref(),
                &hasher,
                &sks[i % c],
            ));
        }
        Self {
            transactions,
            accounts,
        }
    }
}

pub struct MerkleParams<H> {
    pub depth: usize,
    pub hasher: H,
}

pub struct RollupBenchParams<E, H>
where
    E: JubjubEngine,
{
    pub jj_params: Rc<<E as JubjubEngine>::Params>,
    pub sig_hasher: Pedersen<E>,
    pub gen: FixedGenerators,
    pub n_tx: usize,
    pub set_params: MerkleParams<H>,
}

pub struct RollupBench<E, H>
where
    E: JubjubEngine,
    H: Hasher,
{
    pub input: Option<RollupBenchInputs<E, H>>,
    pub params: RollupBenchParams<E, H>,
}

impl<E, H> RollupBench<E, H>
where
    E: JubjubEngine,
    H: Hasher<F = E::Fr>,
{
    pub fn from_counts(
        c: usize,
        t: usize,
        jj_params: <E as JubjubEngine>::Params,
        tree_hash: H,
    ) -> Self {
        let jj_params = Rc::new(jj_params);
        let params = RollupBenchParams {
            jj_params: jj_params.clone(),
            sig_hasher: Pedersen {
                params: jj_params.clone(),
            },
            gen: FixedGenerators::SpendingKeyGenerator,
            n_tx: t,
            set_params: MerkleParams {
                depth: c,
                hasher: tree_hash,
            },
        };
        Self {
            input: Some(RollupBenchInputs::from_counts(c, t, &params)),
            params,
        }
    }
}

impl<E, H> Circuit<E> for RollupBench<E, H>
where
    E: JubjubEngine,
    H: CircuitHasher<E = E> + Hasher<F = E::Fr>,
{
    fn synthesize<CS: ConstraintSystem<E>>(self, cs: &mut CS) -> CResult<()> {
        let gen_value = self
            .params
            .jj_params
            .generator(FixedGenerators::SpendingKeyGenerator);
        let gen: EdwardsPoint<E> = allocate_point::<E, PrimeOrder, _>(
            cs.namespace(|| "gen"),
            Some(gen_value),
            &self.params.jj_params,
        )?;
        let mut removed_accounts = Vec::new();
        let mut inserted_accounts = Vec::new();
        for tx_i in 0..self.params.n_tx {
            let mut cs = cs.namespace(|| format!("tx {}", tx_i));
            let signed_tx = CircuitSignedTx::alloc(
                cs.namespace(|| "alloc"),
                self.input.as_ref().map(|i| &i.transactions[tx_i]),
                (),
                &self.params.jj_params.clone(),
            )?;
            signed_tx.check_signature(
                cs.namespace(|| "check sig"),
                &self.params.sig_hasher,
                gen.clone(),
            )?;
            let src_init = allocate_account(
                cs.namespace(|| "src_init"),
                self.input.as_ref().map(|i| &i.accounts),
                signed_tx.src.clone(),
                Some(signed_tx.action.tx_no.clone()),
                self.params.jj_params.as_ref(),
            )?;
            let dst_init = allocate_account(
                cs.namespace(|| "dst_init"),
                self.input.as_ref().map(|i| &i.accounts),
                signed_tx.action.dst.clone(),
                None,
                self.params.jj_params.as_ref(),
            )?;
            let src_final =
                src_init.with_less(cs.namespace(|| "src delta"), &signed_tx.action.amt)?;
            let dst_final =
                dst_init.with_more(cs.namespace(|| "dst delta"), &signed_tx.action.amt)?;
            removed_accounts.push(src_init);
            removed_accounts.push(dst_init);
            inserted_accounts.push(src_final);
            inserted_accounts.push(dst_final);
        }

        let hasher = self.params.set_params.hasher.clone();
        let insertions = inserted_accounts
            .into_iter()
            .map(|act| act.as_elems())
            .collect::<Vec<_>>();
        let removals = removed_accounts
            .into_iter()
            .map(|act| act.as_elems())
            .collect::<Vec<_>>();

        let set = MerkleCircuitSet::alloc(
            cs.namespace(|| "set init"),
            self.input.as_ref().map(|is| &is.accounts.set),
            hasher,
            &self.params.set_params.depth,
        )?;
        set.inputize(cs.namespace(|| "initial_state input"))?;
        let new_set = set.swap_all(
            cs.namespace(|| "swap"),
            removals
                .into_iter()
                .map(hash::circuit::MaybeHashed::from_values)
                .collect(),
            insertions
                .into_iter()
                .map(hash::circuit::MaybeHashed::from_values)
                .collect(),
        )?;

        new_set.inputize(cs.namespace(|| "final_state input"))?;
        Ok(())
    }
}
