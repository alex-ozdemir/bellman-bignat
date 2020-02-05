use flate2::{Compression, read::GzDecoder, write::GzEncoder};
use group::SemiGroup;
use num_bigint::BigUint;
use rug::{Assign, Integer, ops::Pow};
use serde::{Deserialize,Serialize};

use std::collections::BTreeMap;
use std::convert::AsRef;
use std::fs::File;
use std::io::{BufRead, BufReader};
use std::ops::{Index, MulAssign, RemAssign};
use std::path::PathBuf;

use super::int_set::IntSet;

#[derive(Debug,Deserialize,Serialize,PartialEq,Eq)]
/// A comb of precomputed powers of a base, plus optional precomputed tables of combinations
pub struct PrecompBases {
    /// The values
    bases: Vec<Integer>,
    m: Integer,
    lms: usize,
    bpe: usize,
    tables: Vec<Vec<Integer>>,
    npt: usize,
}

/// pcb[idx] is the idx'th precomputed table
impl Index<usize> for PrecompBases {
    type Output = Vec<Integer>;

    fn index(&self, idx: usize) -> &Self::Output {
        &self.tables[idx]
    }
}

/// turning PrecompBases into a ref returns a slice of the bases (not precomputed tables!)
impl AsRef<[Integer]> for PrecompBases {
    fn as_ref(&self) -> &[Integer] {
        self.bases.as_ref()
    }
}

impl Default for PrecompBases {
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

impl PrecompBases {
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
            bases: ifile
                .lines()
                .map(|x| Integer::from_str_radix(x.unwrap().as_ref(), 16).unwrap())
                .collect(),
            m: modulus,
            lms: log_max_size,
            bpe: log_bits_per_elm,
            tables: Vec::new(),
            npt: 0,
        };
        ret._check();
        ret
    }

    /// build tables from bases
    pub fn make_tables(&mut self, n_per_table: usize) {
        // parallel table building with Rayon
        use rayon::prelude::*;

        // reset tables and n_per_table
        self.tables.clear();
        self.npt = n_per_table;
        if n_per_table == 0 {
            return;
        }

        // for each n bases, compute powerset of values
        self.tables.reserve(self.bases.len() / n_per_table + 1);
        self.tables.par_extend(self.bases.par_chunks(n_per_table).map({
            let modulus = &self.m; // borrow checker can't see into closures; borrow here instead
            move |x| _make_table(x, modulus)
        }));
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
    pub fn n_tables(&self) -> usize {
        self.tables.len()
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
        // this works because we enforce self.bases.len() is power of two
        self.bases.len().trailing_zeros() as usize
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
        self.tables.iter()
    }

    /// return the modulus
    pub fn modulus(&self) -> &Integer {
        &self.m
    }

    // ** internal ** //
    // internal consistency checks --- fn should be called on any newly created object
    fn _check(&self) {
        assert!(self.bases.len().is_power_of_two());
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
    for bnum in 1..bases.len() {
        let base_idx = 1 << bnum;
        // multiply bases[bnum] by the first base_idx elms of ret
        let (src, dst) = ret.split_at_mut(base_idx);
        for idx in 0..base_idx {
            dst[idx].assign(&src[idx] * &bases[bnum]);
            dst[idx].rem_assign(modulus);
        }
    }

    ret
}

/// ParallelExpSet uses precomputed tables to do deletions
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct ParallelExpSet<G: SemiGroup> {
    group: G,
    elements: BTreeMap<Integer, usize>,
    digest: Option<G::Elem>,
}

impl<G: SemiGroup> IntSet for ParallelExpSet<G>
where
    G::Elem: Ord,
{
    type G = G;

    fn new(group: G) -> Self {
        Self {
            digest: Some(group.generator()),
            elements: BTreeMap::new(),
            group,
        }
    }

    fn new_with<I: IntoIterator<Item = BigUint>>(group: G, items: I) -> Self {
        let mut this = Self::new(group);
        this.insert_all(items);
        this
    }

    fn insert(&mut self, n: BigUint) {
        if let Some(ref mut d) = self.digest {
            *d = self.group.power(d, &n);
        }
        *self.elements.entry(_from_biguint(&n)).or_insert(0) += 1;
    }

    fn remove(&mut self, n: &BigUint) -> bool {
        let int_n = _from_biguint(n);
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
            let _expt = {
                let mut tmp = Vec::with_capacity(self.elements.len() + 1);
                tmp.par_extend(self.elements.par_iter().map(|(elem, ct)| Integer::from(elem.pow(*ct as u32))));
                _parallel_multiply(&mut tmp);
                tmp.pop().unwrap()
            };

            // step 2: split exponent into pieces
            // for this, we need to know comb spacing
        }
        self.digest.clone().unwrap()
    }

    fn group(&self) -> &G {
        &self.group
    }
}

fn _from_biguint(n: &BigUint) -> Integer {
    Integer::from_str_radix(n.to_str_radix(32).as_ref(), 32).unwrap()
}

fn _parallel_multiply(v: &mut Vec<Integer>) {
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
    use super::*;

    #[test]
    fn precomp_table() {
        let n_elms = 8;
        let mut pc = PrecompBases::default();
        pc.make_tables(n_elms);
        assert!(pc.n_tables() > 0);

        let num_tables = pc.as_ref().len() / n_elms +
            if pc.as_ref().len() % n_elms == 1 {
                1
            } else {
                0
            };

        assert!(pc.n_tables() == num_tables);
        assert!(pc[0].len() == (1 << n_elms));
    }

    #[test]
    fn precomp_serdes() {
        let pc = {
            let mut tmp = PrecompBases::default();
            tmp.make_tables(4);
            tmp
        };
        pc.serialize("/tmp/serialized.gz");
        let pc2 = PrecompBases::deserialize("/tmp/serialized.gz");
        assert_eq!(pc, pc2);
    }

    #[test]
    fn pmul_test() {
        const NELMS: usize = 2222;
        use rug::rand::RandState;
        let mut rnd = RandState::new();
        let mut v = Vec::with_capacity(NELMS);
        (0..NELMS).for_each(|_| v.push(Integer::from(Integer::random_bits(2048, &mut rnd))));

        // sequential
        let mut prod = Integer::from(1);
        v.iter().for_each(|p| prod.mul_assign(p));

        // parallel
        _parallel_multiply(&mut v);

        assert!(prod == v[0]);
    }
}
