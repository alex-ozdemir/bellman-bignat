use rand::Rng;

use num_bigint::BigUint;

use sapling_crypto::bellman::{Circuit, ConstraintSystem, SynthesisError};
use sapling_crypto::circuit::ecc::EdwardsPoint;
use sapling_crypto::circuit::num::AllocatedNum;
use sapling_crypto::eddsa::{PrivateKey, PublicKey};
use sapling_crypto::jubjub::edwards::Point;
use sapling_crypto::jubjub::{FixedGenerators, JubjubEngine, JubjubParams, PrimeOrder};

use bignat::BigNat;
use gadget::Gadget;
use group::{CircuitRsaGroupParams, CircuitRsaQuotientGroup, RsaQuotientGroup};
use hash;
use hash::circuit::CircuitHasher;
use hash::hashes::Pedersen;
use hash::Hasher;
use rollup::sig::allocate_point;
use rollup::tx::circuit::{CircuitSignedTx, CircuitAccount};
use rollup::tx::{Action, SignedTx, Tx, Account, TxAccountChanges};
use set::int_set::NaiveExpSet;
use set::rsa::{CircuitSet, CircuitSetParams, Set};
use set::{CircuitGenSet, GenSet};
use usize_to_f;
use CResult;
use OptionExt;

use std::collections::HashMap;
use std::rc::Rc;
use std::str::FromStr;

const RSA_2048: &str = "25195908475657893494027183240048398571429282126204032027777137836043662020707595556264018525880784406918290641249515082189298559149176184502808489120072844992687392807287776735971418347270261896375014971824691165077613379859095700097330459748808428401797429100642458691817195118746121515172654632282216869987549182422433637259085141865462043576798423387184774447920739934236584823824281198163815010674810451660377306056201619676256133844143603833904414952634432190114657544454178424020924616515723350778707749817125772467962926386356373289912154831438167899885040445364023527381951378636564391212010397122822120720357";

#[derive(Derivative)]
#[derivative(Clone(bound = ""))]
#[derivative(Debug(bound = ""))]
pub struct Accounts<E, H>
where
    E: JubjubEngine,
    H: Hasher<F = E::Fr>,
{
    map: HashMap<Vec<u8>, Account<E>>,
    set: Set<H, NaiveExpSet<RsaQuotientGroup>>,
}

impl<H, E> Accounts<E, H>
where
    E: JubjubEngine,
    H: Hasher<F = E::Fr>,
{
    pub fn new(s: &RsaParams<H>) -> Self {
        Self {
            map: HashMap::new(),
            set: Set::new_with(
                s.group.clone(),
                hash::rsa::offset(s.n_bits_elem),
                s.hasher.clone(),
                s.n_bits_elem,
                s.limb_width,
                vec![],
            ),
        }
    }

    pub fn insert(&mut self, a: Account<E>) -> Option<Account<E>> {
        let mut key = Vec::new();
        a.id.write(&mut key).unwrap();
        self.set.insert(a.as_elems());
        self.map.insert(key, a)
    }

    pub fn get(&self, k: &PublicKey<E>) -> Option<&Account<E>> {
        let mut key = Vec::new();
        k.write(&mut key).unwrap();
        self.map.get(&key)
    }

    pub fn remove(&mut self, k: &PublicKey<E>) -> Option<Account<E>> {
        let mut key = Vec::new();
        k.write(&mut key).unwrap();
        let r = self.map.remove(&key);
        if let Some(ref r) = r {
            self.set.remove(&r.as_elems());
        }
        r
    }

    pub fn digest(&mut self) -> BigUint {
        self.set.digest()
    }

    /// Applies this transaction to the accounts:
    ///    * mutating the state and
    ///    * returning the changes made
    pub fn apply_tx(&mut self, t: &Tx<E>) -> Option<TxAccountChanges<E>> {
        let dst_init = self.remove(&t.action.dst)?;
        let src_init = self.remove(&t.src)?;
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
        self.insert(src_final.clone());
        self.insert(dst_final.clone());
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
    H: Hasher<F = E::Fr> + CircuitHasher<E = E>,
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
    H: Hasher<F = E::Fr> + CircuitHasher<E = E>,
{
    /// The transactions to do
    pub transactions: Vec<SignedTx<E>>,
    /// The initial account state
    pub accounts: Accounts<E, H>,
    /// The expected final state
    pub final_digest: BigUint,
}

impl<E, H> RollupBenchInputs<E, H>
where
    E: JubjubEngine,
    H: Hasher<F = E::Fr> + CircuitHasher<E = E>,
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
        let mut accounts = Accounts::new(&p.set_params);
        for i in 0..c {
            let account = Account {
                id: pks[i].clone(),
                amt: if i == 0 { 1 } else { 0 },
                next_tx_no: 0,
            };
            accounts.insert(account);
        }
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
        let final_digest = {
            let mut accounts = accounts.clone();
            for t in &transactions {
                accounts.apply_tx(&t.tx);
            }
            accounts.digest()
        };
        Self {
            transactions,
            accounts,
            final_digest,
        }
    }
}

pub struct RsaParams<H> {
    pub group: RsaQuotientGroup,
    pub limb_width: usize,
    pub n_bits_base: usize,
    pub n_bits_elem: usize,
    pub n_bits_challenge: usize,
    pub hasher: H,
}

pub struct RollupBenchParams<E, H>
where
    E: JubjubEngine,
    H: Hasher<F = E::Fr> + CircuitHasher<E = E>,
{
    pub jj_params: Rc<<E as JubjubEngine>::Params>,
    pub sig_hasher: Pedersen<E>,
    pub gen: FixedGenerators,
    pub n_tx: usize,
    pub set_params: RsaParams<H>,
}

pub struct RollupBench<E, H>
where
    E: JubjubEngine,
    H: Hasher<F = E::Fr> + CircuitHasher<E = E>,
{
    pub input: Option<RollupBenchInputs<E, H>>,
    pub params: RollupBenchParams<E, H>,
}

impl<E, H> RollupBench<E, H>
where
    E: JubjubEngine,
    H: Hasher<F = E::Fr> + CircuitHasher<E = E>,
{
    pub fn from_counts(
        c: usize,
        t: usize,
        jj_params: <E as JubjubEngine>::Params,
        set_hash: H,
    ) -> Self {
        let jj_params = Rc::new(jj_params);
        let params = RollupBenchParams {
            jj_params: jj_params.clone(),
            sig_hasher: Pedersen {
                params: jj_params.clone(),
            },
            gen: FixedGenerators::SpendingKeyGenerator,
            n_tx: t,
            set_params: RsaParams {
                group: RsaQuotientGroup {
                    g: BigUint::from(2usize),
                    m: BigUint::from_str(RSA_2048).unwrap(),
                },
                limb_width: 32,
                n_bits_base: 2048,
                n_bits_challenge: 256,
                n_bits_elem: 2048,
                hasher: set_hash,
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
    H: Hasher<F = E::Fr> + CircuitHasher<E = E>,
{
    fn synthesize<CS: ConstraintSystem<E>>(mut self, cs: &mut CS) -> CResult<()> {
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

        let insertions = inserted_accounts
            .into_iter()
            .enumerate()
            .map(|(i, act)| {
                let elems = act.as_elems();
                let hash = self
                    .params
                    .set_params
                    .hasher
                    .allocate_hash(cs.namespace(|| format!("insert hash {}", i)), &elems)?;
                Ok(hash::circuit::MaybeHashed::new(elems, hash))
            })
            .collect::<CResult<Vec<_>>>()?;
        let removals = removed_accounts
            .into_iter()
            .enumerate()
            .map(|(i, act)| {
                let elems = act.as_elems();
                let hash = self
                    .params
                    .set_params
                    .hasher
                    .allocate_hash(cs.namespace(|| format!("remove hash {}", i)), &elems)?;
                Ok(hash::circuit::MaybeHashed::new(elems, hash))
            })
            .collect::<CResult<Vec<_>>>()?;

        let limb_width = self.params.set_params.limb_width;
        let n_bits_base = self.params.set_params.n_bits_base;
        let expected_initial_digest = BigNat::alloc_from_nat(
            cs.namespace(|| "expected_initial_digest"),
            || Ok(self.input.as_mut().ok_or(SynthesisError::AssignmentMissing)?.accounts.digest()),
            limb_width,
            n_bits_base / limb_width,
        )?;
        let expected_final_digest = BigNat::alloc_from_nat(
            cs.namespace(|| "expected_final_digest"),
            || Ok(self.input.as_ref().grab()?.final_digest.clone()),
            self.params.set_params.limb_width,
            self.params.set_params.n_bits_base / self.params.set_params.limb_width,
        )?;

        let mut to_hash_to_challenge: Vec<AllocatedNum<E>> = Vec::new();
        to_hash_to_challenge.extend(
            expected_initial_digest
                .as_limbs::<CS>()
                .into_iter()
                .enumerate()
                .map(|(i, n)| {
                    n.as_sapling_allocated_num(cs.namespace(|| format!("digest hash {}", i)))
                })
                .collect::<Result<Vec<_>, _>>()?,
        );
        to_hash_to_challenge.extend(insertions.iter().map(|i| i.hash.clone().unwrap()));
        to_hash_to_challenge.extend(removals.iter().map(|i| i.hash.clone().unwrap()));
        let challenge = hash::pocklington::hash_to_pocklington_prime(
            cs.namespace(|| "challenge hash"),
            &to_hash_to_challenge,
            self.params.set_params.limb_width,
            self.params.set_params.n_bits_challenge,
            &self.params.set_params.hasher,
        )?;

        let raw_group = self.input.as_ref().map(|s| s.accounts.set.group().clone());
        let group = CircuitRsaQuotientGroup::alloc(
            cs.namespace(|| "group"),
            raw_group.as_ref(),
            (),
            &CircuitRsaGroupParams {
                limb_width: self.params.set_params.limb_width,
                n_limbs: self.params.set_params.n_bits_base / self.params.set_params.limb_width,
            },
        )?;
        group.inputize(cs.namespace(|| "group input"))?;

        let set: CircuitSet<E, H, CircuitRsaQuotientGroup<E>, NaiveExpSet<RsaQuotientGroup>> =
            CircuitSet::alloc(
                cs.namespace(|| "set init"),
                self.input.as_ref().map(|is| &is.accounts.set),
                (group, challenge),
                &CircuitSetParams {
                    hasher: self.params.set_params.hasher.clone(),
                    n_bits: self.params.set_params.n_bits_elem,
                    limb_width: self.params.set_params.limb_width,
                },
            )?;
        set.inputize(cs.namespace(|| "initial_state input"))?;
        set.inner.digest.equal(
            cs.namespace(|| "initial digest matches"),
            &expected_initial_digest,
        )?;

        let new_set = set.swap_all(cs.namespace(|| "swap"), removals, insertions)?;

        new_set
            .inner
            .digest
            .equal(cs.namespace(|| "check"), &expected_final_digest)?;
        new_set.inputize(cs.namespace(|| "final_state input"))?;
        Ok(())
    }
}
