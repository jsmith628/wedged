use super::*;

//
// Dimension casting
//

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

//
//Interpretation casting
//

impl<T:AllocBlade<N,G>, N:Dim, G:Dim> Blade<T,N,G> {

    #[inline(always)]
    pub fn into_simple(self) -> SimpleBlade<T,N,G> where T:AllocSimpleBlade<N,G> {
        SimpleBlade::from_inner_unchecked(self)
    }

    #[inline(always)]
    pub fn into_simple_unchecked(self) -> SimpleBlade<T,N,G> {
        SimpleBlade::from_inner_unchecked(self)
    }

    #[inline(always)]
    pub fn into_unit_unchecked(self) -> UnitBlade<T,N,G> {
        UnitBlade::from_inner_unchecked(self)
    }

}

impl<T:AllocBlade<N,G>, N:Dim, G:Dim> SimpleBlade<T,N,G> {

    #[inline(always)]
    pub fn into_blade(self) -> Blade<T,N,G> {
        self.into_inner()
    }

    #[inline(always)]
    pub fn into_unit_unchecked(self) -> UnitBlade<T,N,G> {
        self.into_blade().into_unit_unchecked()
    }

}

impl<T:AllocBlade<N,G>, N:Dim, G:Dim> UnitBlade<T,N,G> {

    #[inline(always)]
    pub fn into_blade(self) -> Blade<T,N,G> {
        self.into_inner()
    }

    #[inline(always)]
    pub fn into_simple(self) -> SimpleBlade<T,N,G> {
        self.into_blade().into_simple_unchecked()
    }

}

impl<T:AllocEven<N>, N:Dim> Even<T,N> {

    #[inline(always)]
    pub fn into_rotor_unchecked(self) -> Rotor<T,N> {
        Rotor::from_inner_unchecked(self)
    }

    #[inline(always)]
    pub fn into_versor_unchecked(self) -> Versor<T,N> where T:AllocVersor<N> {
        Versor::Even(self.into_rotor_unchecked())
    }

}

impl<T:AllocEven<N>, N:Dim> Rotor<T,N> {
    #[inline(always)] pub fn into_even(self) -> Even<T,N> { self.into_inner() }

    #[inline(always)]
    pub fn into_versor(self) -> Versor<T,N> where T:AllocVersor<N> {
        Versor::Even(self)
    }
}


impl<T:AllocOdd<N>, N:Dim> Odd<T,N> {

    #[inline(always)]
    pub fn into_reflector_unchecked(self) -> Reflector<T,N> {
        Reflector::from_inner_unchecked(self)
    }

    #[inline(always)]
    pub fn into_versor_unchecked(self) -> Versor<T,N> where T:AllocVersor<N> {
        self.into_reflector_unchecked().into_versor()
    }

}

impl<T:AllocOdd<N>, N:Dim> Reflector<T,N> {
    #[inline(always)] pub fn into_odd(self) -> Odd<T,N> { self.into_inner() }

    #[inline(always)]
    pub fn into_versor(self) -> Versor<T,N> where T:AllocVersor<N> {
        Versor::Odd(self)
    }
}

impl<T:AllocVersor<N>, N:Dim> Versor<T,N> {

    pub fn even(&self) -> bool {
        match self {
            Versor::Even(_) => true,
            Versor::Odd(_) => false,
        }
    }

    pub fn try_into_even(self) -> Option<Rotor<T,N>> {
        match self {
            Versor::Even(x) => Some(x),
            Versor::Odd(_) => None
        }
    }

    pub fn unwrap_even(self) -> Rotor<T,N> {
        match self {
            Versor::Even(x) => x,
            Versor::Odd(_) => panic!("Attempted to unwrap an odd versor into a Rotor")
        }
    }

    pub fn odd(&self) -> bool {
        match self {
            Versor::Even(_) => false,
            Versor::Odd(_) => true,
        }
    }

    pub fn try_into_odd(self) -> Option<Reflector<T,N>> {
        match self {
            Versor::Even(_) => None,
            Versor::Odd(x) => Some(x),
        }
    }

    pub fn unwrap_odd(self) -> Reflector<T,N> {
        match self {
            Versor::Even(_) => panic!("Attempted to unwrap an even versor into a Reflector"),
            Versor::Odd(x) => x,
        }
    }

}

impl<T:AllocBlade<N,G>, N:Dim, G:Dim> From<UnitBlade<T,N,G>> for SimpleBlade<T,N,G> {
    fn from(b: UnitBlade<T,N,G>) -> SimpleBlade<T,N,G> { b.into_simple() }
}

impl<T:AllocVersor<N>, N:Dim> From<Rotor<T,N>> for Versor<T,N> {
    fn from(b: Rotor<T,N>) -> Versor<T,N> { b.into_versor() }
}

impl<T:AllocVersor<N>, N:Dim> From<Reflector<T,N>> for Versor<T,N> {
    fn from(b: Reflector<T,N>) -> Versor<T,N> { b.into_versor() }
}

//
//Finding the dual
//

impl<T:AllocBlade<N,G>, N:Dim, G:Dim> SimpleBlade<T,N,G> where
    N:DimSub<G>,
    T:AllocBlade<N,DimDiff<N,G>> + Neg<Output=T>
{

    pub fn dual(self) -> SimpleDualBlade<T,N,G> {
        self.into_inner().dual().into_simple_unchecked()
    }

    pub fn undual(self) -> SimpleDualBlade<T,N,G> {
        self.into_inner().undual().into_simple_unchecked()
    }

}

impl<T:AllocBlade<N,G>, N:Dim, G:Dim> UnitBlade<T,N,G> where
    N:DimSub<G>,
    T:AllocBlade<N,DimDiff<N,G>> + Neg<Output=T>
{

    pub fn dual(self) -> UnitDualBlade<T,N,G> {
        self.into_inner().dual().into_unit_unchecked()
    }

    pub fn undual(self) -> UnitDualBlade<T,N,G> {
        self.into_inner().undual().into_unit_unchecked()
    }

}
