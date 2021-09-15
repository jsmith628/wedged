
use super::*;


impl<T:AllocBlade<N,G>, N:Dim, G:Dim> SimpleBlade<T,N,G> {

    pub fn normalize(self) -> UnitBlade<T,N,G> where
        T: RefMul<T,Output=T> + for<'a> Div<&'a T, Output=T> + ComplexField
    {
        UnitBlade::from_inner_unchecked(self.data.normalize())
    }

    pub fn norm_and_normalize(self) -> (T, UnitBlade<T,N,G>) where
        T: RefMul<T,Output=T> + for<'a> Div<&'a T, Output=T> + ComplexField
    {
        let (l, b) = self.data.norm_and_normalize();
        (l, UnitBlade::from_inner_unchecked(b))
    }

}

impl<T:AllocBlade<N,G>, N:Dim, G:Dim> UnitBlade<T,N,G> {

    pub fn as_simple_blade(self) -> SimpleBlade<T,N,G> {
        SimpleBlade::from_inner_unchecked(self.into_inner())
    }

}
