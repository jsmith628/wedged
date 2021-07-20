
use std::convert::{AsRef, AsMut};
use std::borrow::{Borrow, BorrowMut};
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

pub type Iter<'a, T> = std::slice::Iter<'a, T>;
pub type IterMut<'a, T> = std::slice::IterMut<'a, T>;

pub struct Blade<T:Alloc<N,G>, N:Dim, G:Dim> {
    pub data: Allocate<T,N,G>
}

impl<T:Alloc<N,G>, N:Dim, G:Dim> Blade<T,N,G> {

    pub fn dim_generic(&self) -> N { self.data.dim() }
    pub fn grade_generic(&self) -> G { self.data.grade() }

    pub fn dim(&self) -> usize { self.dim_generic().value() }
    pub fn grade(&self) -> usize { self.dim_generic().value() }

    pub fn as_slice(&self) -> &[T] { self.data.borrow() }
    pub fn as_mut_slice(&mut self) -> &mut [T] { self.data.borrow_mut() }

    pub fn iter(&self) -> Iter<T> { self.as_slice().iter() }
    pub fn iter_mut(&mut self) -> IterMut<T> { self.as_mut_slice().iter_mut() }

}

impl<T:Alloc<N,G>, N:Dim, G:Dim> Clone for Blade<T,N,G> where Allocate<T,N,G>: Clone {
    fn clone(&self) -> Self { Blade { data: self.data.clone() } }
    fn clone_from(&mut self, src: &Self) { self.data.clone_from(&src.data) }
}

impl<T:Alloc<N,G>, N:Dim, G:Dim> Copy for Blade<T,N,G> where Allocate<T,N,G>: Copy {}

impl<T:Alloc<N,G>, N:Dim, G:Dim> AsRef<[T]> for Blade<T,N,G> {
    fn as_ref(&self) -> &[T] { self.data.as_ref() }
}

impl<T:Alloc<N,G>, N:Dim, G:Dim> AsMut<[T]> for Blade<T,N,G> {
    fn as_mut(&mut self) -> &mut [T] { self.data.as_mut() }
}

impl<T:Alloc<N,G>, N:Dim, G:Dim> Borrow<[T]> for Blade<T,N,G> {
    fn borrow(&self) -> &[T] { self.data.borrow() }
}

impl<T:Alloc<N,G>, N:Dim, G:Dim> BorrowMut<[T]> for Blade<T,N,G> {
    fn borrow_mut(&mut self) -> &mut [T] { self.data.borrow_mut() }
}


impl<T:Alloc<N,G>+Eq, N:Dim, G:Dim> Eq for Blade<T,N,G> {}

impl<T, U, N1:Dim, N2:Dim, G1:Dim, G2:Dim> PartialEq<Blade<U,N2,G2>> for Blade<T,N1,G1>
where
    T: Alloc<N1,G1> + PartialEq<U>,
    U: Alloc<N2,G2>
{
    fn eq(&self, rhs:&Blade<U,N2,G2>) -> bool {
        self.dim() == rhs.dim() && self.grade() == rhs.grade() && self.as_slice() == rhs.as_slice()
    }

    fn ne(&self, rhs:&Blade<U,N2,G2>) -> bool {
        self.dim() != rhs.dim() || self.grade() != rhs.grade() || self.as_slice() != rhs.as_slice()
    }
}

impl<T:Alloc<N,G>+Hash, N:Dim, G:Dim> Hash for Blade<T,N,G> {
    fn hash<H:Hasher>(&self, h: &mut H) {
        T::hash_slice(self.borrow(), h)
    }
}

impl<T:Alloc<N,G>, N:Dim, G:Dim> IntoIterator for Blade<T,N,G> {
    type Item = T;
    type IntoIter = <Allocate<T,N,G> as Storage<T,N,G>>::Iter;
    fn into_iter(self) -> Self::IntoIter {
        self.data.into_iter()
    }
}

impl<'a, T:Alloc<N,G>, N:Dim, G:Dim> IntoIterator for &'a Blade<T,N,G> {
    type Item = &'a T;
    type IntoIter = Iter<'a, T>;
    fn into_iter(self) -> Self::IntoIter { self.iter() }
}

impl<'a, T:Alloc<N,G>, N:Dim, G:Dim> IntoIterator for &'a mut Blade<T,N,G> {
    type Item = &'a mut T;
    type IntoIter = IterMut<'a, T>;
    fn into_iter(self) -> Self::IntoIter { self.iter_mut() }
}

impl<T,N:Dim,G1:Dim,G2:Dim> BitXor<Blade<T,N,G2>> for Blade<T,N,G1> where
    T: Mul<T,Output=T> + Alloc<N,G1> + Alloc<N,G2> + Alloc<N,DimSum<G1,G2>>,
    G1: DimAdd<G2>,
{
    type Output = Blade<T,N,DimSum<G1, G2>>;
    fn bitxor(self, rhs: Blade<T,N,G2>) -> Self::Output { unimplemented!() }
}
