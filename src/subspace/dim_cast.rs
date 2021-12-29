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

macro_rules! impl_dim_cast {
    ($Ty:ident<T:$Alloc:ident,$N1:ident $(, $N:ident)*> -> $N2:ident) => {
        impl<T:$Alloc<$N1 $(,$N)*>+Zero, $N1:Dim $(, $N:Dim)*> $Ty<T, $N1 $(,$N)*> {

            pub fn cast_dim_generic_unchecked<N2:Dim>(self, n:N2) -> $Ty<T, $N2 $(,$N)*> where
                T:$Alloc<$N2 $(,$N)*>
            {
                $Ty::from_inner_unchecked(self.into_inner().cast_dim_generic(n))
            }

            pub fn cast_dim_dyn_unchecked(self, n:usize) -> $Ty<T, Dynamic $(,$N)*> where
                T:$Alloc<Dynamic $(,$N)*>
            {
                $Ty::from_inner_unchecked(self.into_inner().cast_dim_dyn(n))
            }

            pub fn cast_dim_unchecked<N2:DimName>(self) -> $Ty<T, $N2 $(,$N)*> where
                T:$Alloc<$N2 $(,$N)*>
            {
                $Ty::from_inner_unchecked(self.into_inner().cast_dim())
            }

            pub fn cast_dim<N2:DimName>(self) -> $Ty<T, $N2 $(,$N)*> where
                T:$Alloc<$N2 $(,$N)*>,
                N1:IsLessOrEqual<N2,Output=True>
            {
                $Ty::from_inner_unchecked(self.into_inner().cast_dim())
            }

        }
    }
}

impl_dim_cast!(UnitBlade<T:AllocBlade,N1,G> -> N2);
impl_dim_cast!(Rotor<T:AllocEven,N1> -> N2);
impl_dim_cast!(Reflector<T:AllocOdd,N1> -> N2);
