use super::*;

impl<T:AllocBlade<N1,G>+Zero, N1:Dim, G:Dim> SimpleBlade<T,N1,G> {

    pub fn cast_dim_generic<N2:Dim>(self, n:N2) -> SimpleBlade<T,N2,G> where T:AllocBlade<N2,G> {
        SimpleBlade::from_inner_unchecked(self.into_inner().cast_dim_generic(n))
    }

    pub fn cast_dim_dyn(self, n:usize) -> SimpleBlade<T,Dynamic,G> where T:AllocBlade<Dynamic,G> {
        SimpleBlade::from_inner_unchecked(self.into_inner().cast_dim_dyn(n))
    }

    pub fn cast_dim<N2:DimName>(self) -> SimpleBlade<T,N2,G> where T:AllocBlade<N2,G> {
        SimpleBlade::from_inner_unchecked(self.into_inner().cast_dim())
    }

}

impl<T:AllocEven<N1>+Zero, N1:Dim> Rotor<T,N1> {

    pub fn cast_dim_generic_unchecked<N2:Dim>(self, n:N2) -> Rotor<T,N2> where T:AllocEven<N2> {
        Rotor::from_inner_unchecked(self.into_inner().cast_dim_generic(n))
    }

    pub fn cast_dim_dyn_unchecked(self, n:usize) -> Rotor<T,Dynamic> where T:AllocEven<Dynamic> {
        Rotor::from_inner_unchecked(self.into_inner().cast_dim_dyn(n))
    }

    pub fn cast_dim_unchecked<N2:DimName>(self) -> Rotor<T,N2> where T:AllocEven<N2> {
        Rotor::from_inner_unchecked(self.into_inner().cast_dim())
    }

    pub fn cast_dim<N2:DimName>(self) -> Rotor<T,N2> where T:AllocEven<N2>, N1:IsLessOrEqual<N2,Output=True> {
        Rotor::from_inner_unchecked(self.into_inner().cast_dim())
    }

}

impl<T:AllocOdd<N1>+Zero, N1:Dim> Reflector<T,N1> {

    pub fn cast_dim_generic_unchecked<N2:Dim>(self, n:N2) -> Reflector<T,N2> where T:AllocOdd<N2> {
        Reflector::from_inner_unchecked(self.into_inner().cast_dim_generic(n))
    }

    pub fn cast_dim_dyn_unchecked(self, n:usize) -> Reflector<T,Dynamic> where T:AllocOdd<Dynamic> {
        Reflector::from_inner_unchecked(self.into_inner().cast_dim_dyn(n))
    }

    pub fn cast_dim_unchecked<N2:DimName>(self) -> Reflector<T,N2> where T:AllocOdd<N2> {
        Reflector::from_inner_unchecked(self.into_inner().cast_dim())
    }

    pub fn cast_dim<N2:DimName>(self) -> Reflector<T,N2> where T:AllocOdd<N2>, N1:IsLessOrEqual<N2,Output=True> {
        Reflector::from_inner_unchecked(self.into_inner().cast_dim())
    }

}
