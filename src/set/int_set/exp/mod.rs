use rug::Integer;

use std::fmt::Debug;

use group::SemiGroup;

pub mod parallel;
pub mod serial;

pub trait Exponentiator<G: SemiGroup>: Sized + Clone + Eq + Debug {
    fn from_group(g: G) -> Self;
    fn exponentiate(&mut self, powers: Vec<Integer>) -> G::Elem;
}
