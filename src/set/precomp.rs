use rug::{Assign, Integer};
use serde::{Deserialize,Serialize};
use std::convert::AsRef;
use std::fs::File;
use std::io::{BufRead, BufReader};
use std::ops::Index;

#[derive(Debug,Deserialize,Serialize)]
/// A comb of precomputed powers of a base, plus optional precomputed tables of combinations
pub struct PrecompBases {
    /// The values
    bases: Vec<Integer>,
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

impl PrecompBases {
    /// read in a file with bases
    pub fn from_file(filename: &str) -> Self {
        Self {
            bases: BufReader::new(File::open(filename).unwrap())
                .lines()
                .map(|x| Integer::from_str_radix(x.unwrap().as_ref(), 16).unwrap())
                .collect(),
            tables: Vec::new(),
            npt: 0,
        }
    }

    /// build tables from bases
    pub fn make_tables(&mut self, n_per_table: usize) {
        // parallel table building with Rayon
        use rayon::prelude::*;

        // for each n bases, compute powerset of values
        self.tables.clear();
        self.tables.reserve(self.bases.len() / n_per_table + 1);
        self.tables.par_extend(self.bases.par_chunks(n_per_table).map(|x| _make_table(x)));
        self.npt = n_per_table;
    }

    /// return number of tables
    pub fn n_tables(&self) -> usize {
        self.tables.len()
    }

    /// return number of bases per precomputed table (i.e., log2(table.len()))
    pub fn n_per_table(&self) -> usize {
        self.npt
    }
}

// make a table from a set of bases
fn _make_table(bases: &[Integer]) -> Vec<Integer> {
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
        }
    }

    ret
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::io::{Read, Write};

    #[test]
    fn precomp_from_file() {
        let pc = PrecompBases::from_file("/tmp/bases.txt");
        assert!(pc.as_ref()[0] == 2);
    }

    #[test]
    fn precomp_and_table() {
        let n_elms = 8;
        let mut pc = PrecompBases::from_file("/tmp/bases.txt");
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
    fn precomp_serialize() {
        let pc = {
            let mut tmp = PrecompBases::from_file("/tmp/bases.txt");
            tmp.make_tables(12);
            tmp
        };
        let buf = bincode::serialize(&pc).unwrap();
        {
            let mut ofile = File::create("/tmp/serialized.txt").unwrap();
            ofile.write_all(&buf[..]).unwrap();
        }
    }

    #[test]
    fn precomp_deserialize() {
        let mut buffer = Vec::new();
        {
            let mut ifile = File::open("/tmp/deser_in.txt").unwrap();
            ifile.read_to_end(&mut buffer).unwrap();
        }
        let pc : PrecompBases = bincode::deserialize(&buffer[..]).unwrap();
        assert!(pc[0].len() == (1 << 12));
    }
}
