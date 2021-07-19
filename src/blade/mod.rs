
use std::borrow::{Borrow};
use std::hash::{Hash, Hasher};
use std::ops::{BitXor, Mul};
use std::iter::{repeat, repeat_with};

use num_traits::Zero;

use na::dimension::{
    Dim, DimAdd, DimSum, DimNameDiff,
    Dynamic, U0, U1, U2, U3, U4, U5, U6
};

use crate::storage::Storage;
use crate::alloc::{Alloc, Allocate};
use crate::DimName;

pub use self::aliases::*;
pub use self::constructors::*;

mod aliases;
mod constructors;

pub struct Blade<T:Alloc<N,G>, N:Dim, G:Dim> {
    pub data: Allocate<T,N,G>
}

impl<T:Alloc<N,G>, N:Dim, G:Dim> Blade<T,N,G> {

    pub fn dim_generic(&self) -> N { self.data.dim() }
    pub fn grade_generic(&self) -> G { self.data.grade() }

    pub fn dim(&self) -> usize { self.dim_generic().value() }
    pub fn grade(&self) -> usize { self.dim_generic().value() }

}

impl<T:Alloc<N,G>, N:Dim, G:Dim> Clone for Blade<T,N,G> where Allocate<T,N,G>: Clone {
    fn clone(&self) -> Self { Blade { data: self.data.clone() } }
    fn clone_from(&mut self, src: &Self) { self.data.clone_from(&src.data) }
}

impl<T:Alloc<N,G>, N:Dim, G:Dim> Copy for Blade<T,N,G> where Allocate<T,N,G>: Copy {}

impl<T:Alloc<N,G>+Eq, N:Dim, G:Dim> Eq for Blade<T,N,G> {}

impl<T, U, N1:Dim, N2:Dim, G1:Dim, G2:Dim> PartialEq<Blade<U,N2,G2>> for Blade<T,N1,G1>
where
    T: Alloc<N1,G1> + PartialEq<U>,
    U: Alloc<N2,G2>
{
    fn eq(&self, rhs:&Blade<U,N2,G2>) -> bool {
        self.dim() == rhs.dim() && self.grade() == rhs.grade() &&
        self.data.borrow() == rhs.data.borrow()
    }

    fn ne(&self, rhs:&Blade<U,N2,G2>) -> bool {
        self.dim() != rhs.dim() || self.grade() != rhs.grade() ||
        self.data.borrow() != rhs.data.borrow()
    }
}

impl<T:Alloc<N,G>+Hash, N:Dim, G:Dim> Hash for Blade<T,N,G> {
    fn hash<H:Hasher>(&self, h: &mut H) {
        T::hash_slice(self.data.borrow(), h)
    }
}

impl<T,N:Dim,G1:Dim,G2:Dim> BitXor<Blade<T,N,G2>> for Blade<T,N,G1> where
    T: Mul<T,Output=T> + Alloc<N,G1> + Alloc<N,G2> + Alloc<N,DimSum<G1,G2>>,
    G1: DimAdd<G2>,
{
    type Output = Blade<T,N,DimSum<G1, G2>>;
    fn bitxor(self, rhs: Blade<T,N,G2>) -> Self::Output { unimplemented!() }
}
