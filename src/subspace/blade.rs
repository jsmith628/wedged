
use super::*;

impl<T:AllocBlade<N,G>, N:Dim, G:Dim> UnitBlade<T,N,G> {

    pub fn as_simple_blade(self) -> SimpleBlade<T,N,G> {
        SimpleBlade::from_inner_unchecked(self.into_inner())
    }

}
