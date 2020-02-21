use rug::Integer;

use super::Exponentiator;
use group::SemiGroup;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SerialExp<G> {
    group: G,
}

impl<G: SemiGroup> Exponentiator<G> for SerialExp<G> {
    fn from_group(group: G) -> Self {
        Self {
            group
        }
    }
    fn exponentiate(&mut self, powers: Vec<Integer>) -> G::Elem {
        powers.into_iter().fold(self.group.generator().clone(), |acc, power| self.group.power(&acc, &power))
    }
}
