
use super::*;

macro_rules! impl_specific_constructors {
    ($($ty:ident::new($($arg:ident),*);)*) => {
        $(
            impl<T> $ty<T> {
                #[doc = new_docs!($ty::new($($arg),*);)]
                pub const fn new($($arg: T),*) -> $ty<T> {
                    $ty { data: <Self as Deref>::Target::new($($arg),*) }
                }
            }
        )*
    }
}

impl_specific_constructors!{

    SimpleVec1::new(x);
    SimpleVec2::new(x,y);
    SimpleVec3::new(x,y,z);
    SimpleVec4::new(x,y,z,w);
    SimpleVec5::new(x,y,z,w,a);
    SimpleVec6::new(x,y,z,w,a,b);

    SimpleBiVec3::new(x,y,z);
    SimpleTriVec4::new(x,y,z,w);
    SimpleQuadVec5::new(x,y,z,w,a);
    SimplePentVec6::new(x,y,z,w,a,b);

    SimpleBiVec2::new(x);
    SimpleTriVec3::new(x);
    SimpleQuadVec4::new(x);
    SimplePentVec5::new(x);
    SimpleHexVec6::new(x);

}

impl<T:AllocBlade<N,U0>, N:DimName> SimpleScalar<T,N> {

    pub fn new(x:T) -> Self {
        Self::from_inner_unchecked(Scalar::new(x))
    }

}

impl<T:AllocBlade<N,N>, N:DimName> SimplePsuedoScalar<T,N> {

    pub fn new_psuedoscalar(x:T) -> Self {
        Self::from_inner_unchecked(PsuedoScalar::new_psuedoscalar(x))
    }

    pub fn unit_psuedoscalar() -> Self where T:One {
        Self::from_inner_unchecked(PsuedoScalar::unit_psuedoscalar())
    }

}

impl<T:AllocBlade<N,N>, N:DimName> UnitPsuedoScalar<T,N> {

    pub fn unit_psuedoscalar() -> Self where T:One {
        Self::from_inner_unchecked(PsuedoScalar::unit_psuedoscalar())
    }

}
