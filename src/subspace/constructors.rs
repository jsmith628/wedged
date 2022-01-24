
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

    /// Creates a new `SimpleScalar` directly from its component
    ///
    /// ```
    /// use wedged::subspace::*;
    /// use wedged::base::U1;
    ///
    /// let x = 6.2831;
    /// let s = SimpleScalar::<_,U1>::new(x);
    ///
    /// assert_eq!(s.value, x);
    /// ```
    ///
    pub fn new(x:T) -> Self {
        Self::from_inner_unchecked(Scalar::new(x))
    }

}

impl<T:AllocBlade<N,N>, N:DimName> SimplePsuedoScalar<T,N> {

    /// Creates a psuedoscalar directly from its component
    ///
    /// ```
    /// use wedged::subspace::*;
    /// use wedged::base::U3;
    ///
    /// let x = 6.2831;
    /// let s = SimpleBlade::<_,U3,U3>::new_psuedoscalar(x);
    ///
    /// assert_eq!(s.value, x);
    /// assert_eq!(s.grade(), 3);
    /// ```
    ///
    pub fn new_psuedoscalar(x:T) -> Self {
        Self::from_inner_unchecked(PsuedoScalar::new_psuedoscalar(x))
    }

    /// Returns the unit psuedoscalar in dimension `N`
    pub fn unit_psuedoscalar() -> Self where T:One {
        Self::from_inner_unchecked(PsuedoScalar::unit_psuedoscalar())
    }

}

impl<T:AllocBlade<N,N>, N:DimName> UnitPsuedoScalar<T,N> {

    /// Returns the unit psuedoscalar in dimension `N`
    pub fn unit_psuedoscalar() -> Self where T:One {
        Self::from_inner_unchecked(PsuedoScalar::unit_psuedoscalar())
    }

}
