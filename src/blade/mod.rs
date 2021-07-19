
use std::borrow::{Borrow};
use std::hash::{Hash, Hasher};
use std::ops::{BitXor, Mul};
use std::iter::{repeat, repeat_with};

use num_traits::Zero;

use na::base::dimension::{Dynamic, Dim, DimAdd, DimSum};

use crate::storage::Storage;
use crate::alloc::{Alloc, Allocate};
use crate::DimName;

pub use self::aliases::*;

mod aliases;

pub struct Blade<T:Alloc<N,G>, N:Dim, G:Dim> {
    pub data: Allocate<T,N,G>
}

impl<T:Alloc<N,G>, N:Dim, G:Dim> Blade<T,N,G> {

    pub fn dim_generic(&self) -> N { self.data.dim() }
    pub fn grade_generic(&self) -> G { self.data.grade() }

    pub fn dim(&self) -> usize { self.dim_generic().value() }
    pub fn grade(&self) -> usize { self.dim_generic().value() }

    pub fn from_iter_generic<I:IntoIterator<Item=T>>(n:N, g:G, iter: I) -> Self {
        Blade { data: Allocate::<T,N,G>::from_iterator(n, g, iter) }
    }

    pub fn from_index_fn_generic<F: FnMut(usize)->T>(n:N, g:G, f: F) -> Self {
        Self::from_iter_generic(n, g, (0..).into_iter().map(f))
    }

    pub fn from_element_generic(n:N, g:G, x:T) -> Self where T:Clone {
        Self::from_iter_generic(n, g, repeat(x))
    }

    pub fn zeroed_generic(n:N, g:G) -> Self where T:Zero {
        Self::from_iter_generic(n, g, repeat_with(|| T::zero()))
    }

}

impl<T:Alloc<N,G>, N:DimName, G:DimName> Blade<T,N,G> {

    pub fn from_iterator<I:IntoIterator<Item=T>>(iter: I) -> Self {
        Self::from_iter_generic(N::name(), G::name(), iter)
    }

    pub fn from_index_fn<F: FnMut(usize)->T>(f: F) -> Self {
        Self::from_index_fn_generic(N::name(), G::name(), f)
    }

    pub fn from_element(x:T) -> Self where T:Clone {
        Self::from_element_generic(N::name(), G::name(), x)
    }

    pub fn zeroed() -> Self where T:Zero {
        Self::zeroed_generic(N::name(), G::name())
    }

}

impl<T:Alloc<Dynamic,G>, G:DimName> Blade<T,Dynamic,G> {

    pub fn from_iterator<I:IntoIterator<Item=T>>(n:usize, iter: I) -> Self {
        Self::from_iter_generic(Dynamic::new(n), G::name(), iter)
    }

    pub fn from_index_fn<F: FnMut(usize)->T>(n:usize, f: F) -> Self {
        Self::from_index_fn_generic(Dynamic::new(n), G::name(), f)
    }

    pub fn from_element(n:usize, x:T) -> Self where T:Clone {
        Self::from_element_generic(Dynamic::new(n), G::name(), x)
    }

    pub fn zeroed(n:usize) -> Self where T:Zero {
        Self::zeroed_generic(Dynamic::new(n), G::name())
    }

}

impl<T:Alloc<N,Dynamic>, N:DimName> Blade<T,N,Dynamic> {

    pub fn from_iterator<I:IntoIterator<Item=T>>(g:usize, iter: I) -> Self {
        Self::from_iter_generic(N::name(), Dynamic::new(g), iter)
    }

    pub fn from_index_fn<F: FnMut(usize)->T>(g:usize, f: F) -> Self {
        Self::from_index_fn_generic(N::name(), Dynamic::new(g), f)
    }

    pub fn from_element(g:usize, x:T) -> Self where T:Clone {
        Self::from_element_generic(N::name(), Dynamic::new(g), x)
    }

    pub fn zeroed(g:usize) -> Self where T:Zero {
        Self::zeroed_generic(N::name(), Dynamic::new(g))
    }

}

impl<T:Alloc<Dynamic,Dynamic>> Blade<T,Dynamic,Dynamic> {

    pub fn from_iterator<I:IntoIterator<Item=T>>(n:usize, g:usize, iter: I) -> Self {
        Self::from_iter_generic(Dynamic::new(n), Dynamic::new(g), iter)
    }

    pub fn from_index_fn<F: FnMut(usize)->T>(n:usize, g:usize, f: F) -> Self {
        Self::from_index_fn_generic(Dynamic::new(n), Dynamic::new(g), f)
    }

    pub fn from_element(n:usize, g:usize, x:T) -> Self where T:Clone {
        Self::from_element_generic(Dynamic::new(n), Dynamic::new(g), x)
    }

    pub fn zeroed(n:usize, g:usize) -> Self where T:Zero {
        Self::zeroed_generic(Dynamic::new(n), Dynamic::new(g))
    }

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
