
use super::*;

macro_rules! wrap_involute {
    ($($ref_mul:ident)? |$self:ident| $inv:expr) => {

        /// Reverses the order of the vectors in each basis blade
        pub fn reverse(self) -> Self { Self { data: self.data.reverse() } }

        /// Negates `self` of each component with an odd grade
        pub fn involute(self) -> Self { Self { data: self.data.involute() } }

        /// The multiplicative inverse of this element
        pub fn inverse($self) -> Self
        $(where T: $ref_mul)?
        { $inv }

    }
}

impl<T:AllocBlade<N,G>+Neg<Output=T>, N:Dim, G:Dim> SimpleBlade<T,N,G> {
    wrap_involute!(RefDivRing |self| {let l=self.norm_sqrd(); self.reverse() / l} );
}

impl<T:AllocBlade<N,G>+Neg<Output=T>, N:Dim, G:Dim> UnitBlade<T,N,G> { wrap_involute!(|self| self.reverse()); }
impl<T:AllocEven<N>+Neg<Output=T>, N:Dim> Rotor<T,N> { wrap_involute!(|self| self.reverse()); }
impl<T:AllocOdd<N>+Neg<Output=T>, N:Dim> Reflector<T,N> { wrap_involute!(|self| self.reverse()); }

impl<T:AllocVersor<N>+Neg<Output=T>, N:Dim> Versor<T,N> {

    /// Reverses the order of the vectors in each basis blade
    ///
    /// Wraps [`Even::reverse()`] and [`Odd::reverse()`]
    pub fn reverse(self) -> Self {
        match self {
            Versor::Even(r) => Versor::Even(r.reverse()),
            Versor::Odd(r) => Versor::Odd(r.reverse()),
        }
    }

    /// Negates `self` if odd
    ///
    /// Wraps [`Rotor::involute()`] and [`Reflector::involute()`]
    pub fn involute(self) -> Self {
        match self {
            Versor::Even(r) => Versor::Even(r.involute()),
            Versor::Odd(r) => Versor::Odd(r.involute()),
        }
    }

    /// The multiplicative inverse of this element
    ///
    /// Wraps [`Rotor::inverse()`] and [`Reflector::inverse()`]
    pub fn inverse(self) -> Self {
        match self {
            Versor::Even(r) => Versor::Even(r.inverse()),
            Versor::Odd(r) => Versor::Odd(r.inverse()),
        }
    }

}
