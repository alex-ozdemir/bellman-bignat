use flate2::{Compression, read::GzDecoder, write::GzEncoder};
use group::{SemiGroup, RsaGroup, RsaQuotientGroup};
use num_bigint::BigUint;
use num_traits::Num;
use rug::{Assign, Integer, ops::Pow};
use serde::{Deserialize,Serialize};

use std::collections::BTreeMap;
use std::fs::File;
use std::io::{BufRead, BufReader};
use std::ops::{Index, MulAssign, RemAssign};
use std::path::PathBuf;
use std::rc::Rc;

use super::int_set::IntSet;

#[derive(Clone,Debug,Deserialize,Serialize,PartialEq,Eq)]
/// A comb of precomputed powers of a base, plus optional precomputed tables of combinations
pub struct ParExpComb {
    bs: Vec<Integer>,
    m: Integer,
    lms: usize,
    bpe: usize,
    ts: Vec<Vec<Integer>>,
    npt: usize,
}

/// pcb[idx] is the idx'th precomputed table
impl Index<usize> for ParExpComb {
    type Output = Vec<Integer>;

    fn index(&self, idx: usize) -> &Self::Output {
        &self.ts[idx]
    }
}

impl Default for ParExpComb {
    /// get default precomps
    fn default() -> Self {
        // XXX(HACK): we read from $CARGO_MANIFEST_DIR/lib/pcb_dflt
        let dir = std::env::var("CARGO_MANIFEST_DIR").unwrap();
        let mut pbuf = PathBuf::from(dir);
        pbuf.push("lib");
        pbuf.push("pcb_dflt");
        Self::deserialize(pbuf.to_str().unwrap())
    }
}

#[allow(clippy::len_without_is_empty)]
impl ParExpComb {
    // ** initialization and precomputation ** //
    /// read in a file with bases
    pub fn from_file(filename: &str, log_max_size: usize, log_bits_per_elm: usize) -> Self {
        let mut ifile = BufReader::new(File::open(filename).unwrap());
        let modulus = {
            let mut mbuf = String::new();
            ifile.read_line(&mut mbuf).unwrap();
            Integer::from_str_radix(&mbuf, 16).unwrap()
        };
        let ret = Self {
            bs: ifile
                .lines()
                .map(|x| Integer::from_str_radix(x.unwrap().as_ref(), 16).unwrap())
                .collect(),
            m: modulus,
            lms: log_max_size,
            bpe: log_bits_per_elm,
            ts: Vec::new(),
            npt: 0,
        };
        ret._check();
        ret
    }

    /// build tables from bases
    pub fn make_tables(&mut self, n_per_table: usize) {
        // parallel table building with Rayon
        use rayon::prelude::*;

        // n_per_table must be a power of 2 or things get messy
        assert!(n_per_table.is_power_of_two());

        // reset tables and n_per_table
        self.ts.clear();
        self.npt = n_per_table;
        if n_per_table == 0 {
            return;
        }

        // for each n bases, compute powerset of values
        self.ts.reserve(self.bs.len() / n_per_table + 1);
        self.ts.par_extend(self.bs.par_chunks(n_per_table).map({
            // closure would capture borrow of self, which breaks because self is borrowed already.
            // instead, borrow the piece of self we need outside, then move the borrow inside
            // http://smallcultfollowing.com/babysteps/blog/2018/04/24/rust-pattern-precise-closure-capture-clauses/
            let modulus = &self.m;
            move |x| _make_table(x, modulus)
        }));
    }

    // ** exponentiation ** //
    /// Parallel exponentiation using windows and combs
    pub fn exp(&self, expt: Integer) -> Integer {
        use rayon::prelude::*;

        // expt must be positive
        let expt_sign = expt.cmp0();
        assert_ne!(expt_sign, std::cmp::Ordering::Less);
        if expt_sign == std::cmp::Ordering::Equal {
            return Integer::from(1);
        }

        // figure out how many of the tables we'll need to use
        let bits_per_expt = 1 << self.log_spacing();
        let expts_per_table = self.n_per_table();
        let bits_per_table = bits_per_expt * expts_per_table;
        let n_sig_bits = expt.significant_bits() as usize;
        let n_tables = (n_sig_bits + bits_per_table - 1) / bits_per_table;

        // make sure this precomp is big enough!
        assert!(n_sig_bits < (1 << (self.log_max_size() + self.log_bits_per_elm())));
        assert!(n_tables <= self.len());

        // figure out chunk size
        let n_threads = rayon::current_num_threads();
        let tables_per_chunk = (n_tables + n_threads - 1) / n_threads;

        // parallel multiexponentiation
        let modulus = &self.m;
        self.ts[0..n_tables].par_chunks(tables_per_chunk).enumerate().map(|(chunk_idx, ts)| {
            let mut acc = Integer::from(1);
            let n_ts = ts.len();
            let chunk_offset = chunk_idx * tables_per_chunk * bits_per_table;
            for bdx in 0..bits_per_expt {
                for tdx in 0..n_ts {
                    let mut val = 0u32;
                    for edx in 0..expts_per_table {
                        let bitnum = chunk_offset + tdx * bits_per_table + edx * bits_per_expt + bdx;
                        let bit = expt.get_bit(bitnum as u32) as u32;
                        val |= bit << edx;
                    }
                    acc.mul_assign(&ts[tdx][val as usize]);
                    acc.rem_assign(modulus);
                }
                acc.square_mut();
                acc.rem_assign(modulus);
            }
            acc
        }).reduce(|| Integer::from(1), |mut acc, next| {
            acc.mul_assign(&next);
            acc.rem_assign(modulus);
            acc
        })
    }

    // ** serialization ** //
    /// write struct to a file
    pub fn serialize(&self, filename: &str) {
        let output = GzEncoder::new(File::create(filename).unwrap(), Compression::default());
        bincode::serialize_into(output, self).unwrap();
    }

    /// read struct from file
    pub fn deserialize(filename: &str) -> Self {
        let input = GzDecoder::new(File::open(filename).unwrap());
        let ret: Self = bincode::deserialize_from(input).unwrap();
        ret._check();
        ret
    }

    // ** accessors and misc ** //
    /// return number of tables
    pub fn len(&self) -> usize {
        self.ts.len()
    }

    /// return number of bases per precomputed table (i.e., log2(table.len()))
    pub fn n_per_table(&self) -> usize {
        self.npt
    }

    /// log of the max size of the accumulator these tables accommodate
    pub fn log_max_size(&self) -> usize {
        self.lms
    }

    /// log of the number of bases in this struct
    pub fn log_num_bases(&self) -> usize {
        // this works because we enforce self.bs.len() is power of two
        self.bs.len().trailing_zeros() as usize
    }

    /// log of the number of bits per elm in the accumulator these tables accommodate
    pub fn log_bits_per_elm(&self) -> usize {
        self.bpe
    }

    /// spacing between successive exponents
    pub fn log_spacing(&self) -> usize {
        self.log_max_size() - self.log_num_bases() + self.log_bits_per_elm()
    }

    /// return iterator over tables
    pub fn iter(&self) -> std::slice::Iter<Vec<Integer>> {
        self.ts.iter()
    }

    /// ref to bases
    pub fn bases(&self) -> &[Integer] {
        &self.bs[..]
    }

    /// ref to modulus
    pub fn modulus(&self) -> &Integer {
        &self.m
    }

    // ** internal ** //
    // internal consistency checks --- fn should be called on any newly created object
    fn _check(&self) {
        assert!(self.bs.len().is_power_of_two());
    }
}

// make a table from a set of bases
fn _make_table(bases: &[Integer], modulus: &Integer) -> Vec<Integer> {
    let mut ret = vec!(Integer::new(); 1 << bases.len());
    // base case: 0 and 1
    ret[0].assign(1);
    ret[1].assign(&bases[0]);

    // compute powerset of bases
    // for each element in bases
    for (bnum, base) in bases.iter().enumerate().skip(1) {
        let base_idx = 1 << bnum;
        // multiply bases[bnum] by the first base_idx elms of ret
        let (src, dst) = ret.split_at_mut(base_idx);
        for idx in 0..base_idx {
            dst[idx].assign(&src[idx] * base);
            dst[idx].rem_assign(modulus);
        }
    }

    ret
}

// ** utility traits ** //

pub trait IntegerConversion {
    fn to_integer(&Self) -> Integer;
    fn from_integer(&Integer) -> Self;
}

impl IntegerConversion for BigUint {
    fn to_integer(n: &BigUint) -> Integer {
        Integer::from_str_radix(n.to_str_radix(32).as_ref(), 32).unwrap()
    }

    fn from_integer(n: &Integer) -> BigUint {
        BigUint::from_str_radix(n.to_string_radix(32).as_ref(), 32).unwrap()
    }
}

pub trait IntoElem: SemiGroup {
    fn into_elem(&self, <Self as SemiGroup>::Elem) -> <Self as SemiGroup>::Elem;
}

impl IntoElem for RsaGroup {
    fn into_elem(&self, n: BigUint) -> BigUint {
        &n % &self.m
    }
}

impl IntoElem for RsaQuotientGroup {
    fn into_elem(&self, mut n: BigUint) -> BigUint {
        n = &n % &self.m;
        let y = &self.m - &n;
        std::cmp::min(n, y)
    }
}

// ** ParallelExpSet ** //

/// ParallelExpSet uses precomputed tables to speed up rebuilding the set
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct ParallelExpSet<G: SemiGroup> {
    group: G,
    elements: BTreeMap<Integer, usize>,
    digest: Option<Integer>,
    comb: Rc<ParExpComb>,    // NOTE: does this need to be Arc?
}

impl<G: SemiGroup> ParallelExpSet<G> {
    const N_PER_TABLE: usize = 8;

    pub fn clear_digest(&mut self) {
        self.digest = None;
    }
}

impl<G: SemiGroup> IntSet for ParallelExpSet<G>
where
    G::Elem: Ord + IntegerConversion,
    G: IntoElem,
{
    type G = G;

    fn new(group: G) -> Self {
        let mut pc = ParExpComb::default();
        pc.make_tables(Self::N_PER_TABLE);
        Self {
            digest: None,   // start with None so that new_with builds in parallel by default
            elements: BTreeMap::new(),
            group,
            comb: Rc::new(pc)
        }
    }

    // FIXME? insert_all will insert one by one. This is slow if you're inserting
    //        lots of elements at once, say, more than 1/4 of the current size.
    //        In this case, you can call clear_digest() to clear the digest first.

    fn new_with<I: IntoIterator<Item = BigUint>>(group: G, items: I) -> Self {
        let mut this = Self::new(group);
        this.insert_all(items);
        this
    }

    fn insert(&mut self, n: BigUint) {
        let int_n = <BigUint as IntegerConversion>::to_integer(&n);
        if let Some(ref mut d) = self.digest {
            d.mul_assign(&int_n);
            d.rem_assign(&self.comb.m);
        }
        *self.elements.entry(int_n).or_insert(0) += 1;
    }

    fn remove(&mut self, n: &BigUint) -> bool {
        let int_n = <BigUint as IntegerConversion>::to_integer(&n);
        if let Some(count) = self.elements.get_mut(&int_n) {
            *count -= 1;
            if *count == 0 {
                self.elements.remove(&int_n);
            }
            self.digest = None;
            true
        } else {
            false
        }
    }

    fn digest(&mut self) -> G::Elem {
        use rayon::prelude::*;

        if self.digest.is_none() {
            // step 1: compute the exponent
            let expt = {
                let mut tmp = Vec::with_capacity(self.elements.len() + 1);
                tmp.par_extend(self.elements.par_iter().map(|(elem, ct)| Integer::from(elem.pow(*ct as u32))));
                _parallel_product(&mut tmp);
                tmp.pop().unwrap()
            };

            // step 2: exponentiate using ParExpComb
            self.digest = Some(self.comb.exp(expt));
        }

        // convert internal Integer repr to Elem repr, respecting structure of group via IntoElem
        self.group.into_elem(<G::Elem as IntegerConversion>::from_integer(&self.digest.as_ref().unwrap()))
    }

    fn group(&self) -> &G {
        &self.group
    }
}

fn _parallel_product(v: &mut Vec<Integer>) {
    use rayon::prelude::*;

    if v.len() % 2 == 1 {
        v.push(Integer::from(1));
    }

    while v.len() > 1 {
        // invariant: length of list is always even
        assert!(v.len() % 2 == 0);

        // split the list in half; multiply first half by second half in parallel
        let split_point = v.len() / 2;
        let (fst, snd) = v.split_at_mut(split_point);
        fst.par_iter_mut().zip(snd).for_each(|(f, s)| f.mul_assign(s as &Integer));

        // cut length of list in half, possibly padding with an extra '1'
        if split_point != 1 && split_point % 2 == 1 {
            v.truncate(split_point + 1);
            v[split_point].assign(1);
        } else {
            v.truncate(split_point);
        }
    }

    assert!(v.len() == 1);
}

#[cfg(test)]
mod tests {
    use rug::rand::RandState;
    use super::*;

    #[test]
    fn precomp_table() {
        const NELMS: usize = 8;

        let mut pc = ParExpComb::default();
        pc.make_tables(NELMS);
        assert!(pc.len() > 0);

        let num_tables = (pc.bases().len() + NELMS - 1) / NELMS;
        assert!(pc.len() == num_tables);
        assert!(pc[0].len() == (1 << NELMS));

        // check the first precomputed table for correctness
        let bases = pc.bases();
        let modulus = pc.modulus();
        for idx in 0..(1 << NELMS) {
            let mut accum = Integer::from(1);
            for jdx in 0..NELMS {
                if idx & (1 << jdx) != 0 {
                    accum.mul_assign(&bases[jdx]);
                    accum.rem_assign(modulus);
                }
            }
            assert_eq!(&accum, &pc[0][idx]);
        }
    }

    #[test]
    fn precomp_serdes() {
        let pc = {
            let mut tmp = ParExpComb::default();
            tmp.make_tables(4);
            tmp
        };
        pc.serialize("/tmp/serialized.gz");
        let pc2 = ParExpComb::deserialize("/tmp/serialized.gz");
        assert_eq!(pc, pc2);
    }

    #[test]
    fn pprod_test() {
        const NELMS: usize = 2222;

        let mut rnd = RandState::new();
        let mut v = Vec::with_capacity(NELMS);
        (0..NELMS).for_each(|_| v.push(Integer::from(Integer::random_bits(2048, &mut rnd))));

        // sequential
        let mut prod = Integer::from(1);
        v.iter().for_each(|p| prod.mul_assign(p));

        // parallel
        _parallel_product(&mut v);

        assert!(prod == v[0]);
    }
}
