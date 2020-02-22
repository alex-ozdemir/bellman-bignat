use rug::Integer;

use std::fmt::Debug;

use group::SemiGroup;

pub mod parallel;
pub mod serial;

pub trait Exponentiator<G: SemiGroup>: Sized + Clone + Eq + Debug {
    /// Construct an exponentiator, given the group (which includes a generator)
    fn from_group(g: G) -> Self;
    /// Compute (generator)^(product(powers))
    fn exponentiate(&mut self, powers: Vec<Integer>) -> G::Elem;
}
