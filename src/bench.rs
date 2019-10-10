pub use sapling_crypto::bellman::pairing::Engine;
pub use sapling_crypto::bellman::{
    ConstraintSystem, Index, LinearCombination, SynthesisError, Variable,
};

use std::io::Write;
use std::io::Error;

pub struct ConstraintCounter {
    n_constraints: usize,
}

impl ConstraintCounter {
    pub fn num_constraints(&self) -> usize {
        self.n_constraints
    }
    pub fn new() -> Self {
        Self { n_constraints: 0 }
    }
}

impl<E: Engine> ConstraintSystem<E> for ConstraintCounter {
    type Root = Self;
    fn alloc<F, A, AR>(&mut self, _annotation: A, _f: F) -> Result<Variable, SynthesisError>
    where
        F: FnOnce() -> Result<E::Fr, SynthesisError>,
        A: FnOnce() -> AR,
        AR: Into<String>,
    {
        Ok(Variable::new_unchecked(Index::Aux(0)))
    }
    fn alloc_input<F, A, AR>(&mut self, _annotation: A, _f: F) -> Result<Variable, SynthesisError>
    where
        F: FnOnce() -> Result<E::Fr, SynthesisError>,
        A: FnOnce() -> AR,
        AR: Into<String>,
    {
        Ok(Variable::new_unchecked(Index::Input(0)))
    }

    fn enforce<A, AR, LA, LB, LC>(&mut self, _annotation: A, _a: LA, _b: LB, _c: LC)
    where
        A: FnOnce() -> AR,
        AR: Into<String>,
        LA: FnOnce(LinearCombination<E>) -> LinearCombination<E>,
        LB: FnOnce(LinearCombination<E>) -> LinearCombination<E>,
        LC: FnOnce(LinearCombination<E>) -> LinearCombination<E>,
    {
        self.n_constraints += 1;
    }
    fn push_namespace<NR, N>(&mut self, _name_fn: N)
    where
        NR: Into<String>,
        N: FnOnce() -> NR,
    {
    }
    fn pop_namespace(&mut self) {}
    fn get_root(&mut self) -> &mut Self::Root {
        self
    }
}

mod interner {
    use fnv::FnvHashMap;
    use std::collections::HashMap;
    use std::mem::replace;

    #[derive(Debug, Clone, Copy)]
    pub struct InternedName(usize);

    pub struct Interner {
        strings: FnvHashMap<usize, String>,
        names: HashMap<String, usize>,
        next_name: usize,
    }

    impl Interner {
        pub fn new() -> Self {
            Self {
                strings: FnvHashMap::default(),
                names: HashMap::default(),
                next_name: 0,
            }
        }

        pub fn get_name(&mut self, string: &str) -> InternedName {
            let mut m = replace(&mut self.names, HashMap::new());
            let r = InternedName(
                *m.raw_entry_mut()
                    .from_key(string)
                    .or_insert_with(|| {
                        let id = self.next_name;
                        assert!(self.strings.insert(id, string.to_owned()).is_none());
                        self.next_name += 1;
                        (string.to_owned(), id)
                    })
                    .1,
            );
            self.names = m;
            r
        }

        pub fn get_string(&self, name: InternedName) -> &str {
            self.strings.get(&name.0).unwrap()
        }
    }
}

use self::interner::{InternedName, Interner};

pub struct InternedConstraintProfile {
    count: usize,
    cumulative_count: usize,
    children: Vec<(InternedName, InternedConstraintProfile)>,
}

impl InternedConstraintProfile {
    pub fn new() -> Self {
        Self {
            count: 0,
            cumulative_count: 0,
            children: Vec::new(),
        }
    }

    pub fn increment(&mut self) {
        self.count += 1;
        self.cumulative_count += 1;
    }

    pub fn add_child(&mut self, name: InternedName, child: InternedConstraintProfile) {
        if child.cumulative_count > 0 {
            self.cumulative_count += child.cumulative_count;
            self.children.push((name, child));
        }
    }

    pub fn emit_as_json<W: Write>(&self, w: &mut W, interner: &Interner) -> Result<(), Error>  {
        w.write_all(b"{")?;
        write!(w, "\"_count\":{},\"_cumulative\":{}", self.count, self.cumulative_count)?;
        for (n, c) in &self.children {
            write!(w, ",\"{}\":", interner.get_string(*n))?;
            c.emit_as_json(w, interner)?;
        }
        w.write_all(b"}")?;
        Ok(())
    }
}

pub struct ConstraintProfiler {
    names: Vec<InternedName>,
    profiles: Vec<InternedConstraintProfile>,
    interner: Interner,
}

impl ConstraintProfiler {
    pub fn new() -> Self {
        Self {
            names: vec![],
            profiles: vec![InternedConstraintProfile::new()],
            interner: Interner::new(),
        }
    }

    pub fn emit_as_json<W: Write>(&self, w: &mut W) -> Result<(), Error> {
        assert_eq!(self.profiles.len(), 1);
        self.profiles[0].emit_as_json(w, &self.interner)
    }

    pub fn num_constraints(&self) -> usize {
        assert_eq!(self.profiles.len(), 1);
        self.profiles[0].cumulative_count
    }
}

impl<E: Engine> ConstraintSystem<E> for ConstraintProfiler {
    type Root = Self;
    fn alloc<F, A, AR>(&mut self, _annotation: A, _f: F) -> Result<Variable, SynthesisError>
    where
        F: FnOnce() -> Result<E::Fr, SynthesisError>,
        A: FnOnce() -> AR,
        AR: Into<String>,
    {
        Ok(Variable::new_unchecked(Index::Aux(0)))
    }
    fn alloc_input<F, A, AR>(&mut self, _annotation: A, _f: F) -> Result<Variable, SynthesisError>
    where
        F: FnOnce() -> Result<E::Fr, SynthesisError>,
        A: FnOnce() -> AR,
        AR: Into<String>,
    {
        Ok(Variable::new_unchecked(Index::Input(0)))
    }

    fn enforce<A, AR, LA, LB, LC>(&mut self, _annotation: A, _a: LA, _b: LB, _c: LC)
    where
        A: FnOnce() -> AR,
        AR: Into<String>,
        LA: FnOnce(LinearCombination<E>) -> LinearCombination<E>,
        LB: FnOnce(LinearCombination<E>) -> LinearCombination<E>,
        LC: FnOnce(LinearCombination<E>) -> LinearCombination<E>,
    {
        self.profiles.last_mut().unwrap().increment();
    }

    fn push_namespace<NR, N>(&mut self, _name_fn: N)
    where
        NR: Into<String>,
        N: FnOnce() -> NR,
    {
        let string: String = _name_fn().into();
        let name = self.interner.get_name(&string);
        self.profiles.push(InternedConstraintProfile::new());
        self.names.push(name);
        debug_assert!(self.profiles.len() == self.names.len() + 1);
    }

    fn pop_namespace(&mut self) {
        debug_assert!(self.names.len() > 0);
        debug_assert!(self.profiles.len() > 0);
        let n = self.names.pop().unwrap();
        let p = self.profiles.pop().unwrap();
        self.profiles.last_mut().unwrap().add_child(n, p);
        debug_assert!(self.profiles.len() > 0);
        debug_assert!(self.profiles.len() == self.names.len() + 1);
    }

    fn get_root(&mut self) -> &mut Self::Root {
        self
    }
}
