
use super::*;

macro_rules! wrap_involute {
    ($($ref_mul:ident)? |$self:ident| $inv:expr) => {

        pub fn reverse(self) -> Self { Self { data: self.data.reverse() } }
        pub fn involute(self) -> Self { Self { data: self.data.involute() } }

        pub fn inverse($self) -> Self
        $(where T: $ref_mul)?
        { $inv }

    }
}

impl<T:AllocBlade<N,G>+Neg<Output=T>, N:Dim, G:Dim> SimpleBlade<T,N,G> {
    wrap_involute!(RefComplexField |self| {let l=self.norm_sqrd(); self.reverse() / l} );
}

impl<T:AllocBlade<N,G>+Neg<Output=T>, N:Dim, G:Dim> UnitBlade<T,N,G> { wrap_involute!(|self| self.reverse()); }
impl<T:AllocEven<N>+Neg<Output=T>, N:Dim> Rotor<T,N> { wrap_involute!(|self| self.reverse()); }
impl<T:AllocOdd<N>+Neg<Output=T>, N:Dim> Reflector<T,N> { wrap_involute!(|self| self.reverse()); }

impl<T:AllocVersor<N>+Neg<Output=T>, N:Dim> Versor<T,N> {

    pub fn reverse(self) -> Self {
        match self {
            Versor::Even(r) => Versor::Even(r.reverse()),
            Versor::Odd(r) => Versor::Odd(r.reverse()),
        }
    }

    pub fn involute(self) -> Self {
        match self {
            Versor::Even(r) => Versor::Even(r.involute()),
            Versor::Odd(r) => Versor::Odd(r.involute()),
        }
    }

    pub fn inverse(self) -> Self {
        match self {
            Versor::Even(r) => Versor::Even(r.inverse()),
            Versor::Odd(r) => Versor::Odd(r.inverse()),
        }
    }

}
