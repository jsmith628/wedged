
use std::convert::{AsRef, AsMut};
use std::borrow::{Borrow, BorrowMut};
use std::ops::{Index, IndexMut};
use std::mem::{MaybeUninit, transmute, transmute_copy};
use std::iter::{
    IntoIterator, FromIterator,
    DoubleEndedIterator, ExactSizeIterator, FusedIterator,
    //TrustedLen
};

use na::base::dimension::{Dim, DimName};

use crate::binom;

pub unsafe trait Storage<T, N:Dim, G:Dim>:
    Index<usize, Output=T> + IndexMut<usize> +
    AsRef<[T]> + AsMut<[T]> +
    Borrow<[T]> + BorrowMut<[T]> +
    IntoIterator<Item=T, IntoIter=Self::Iter>
{
    type Uninit: UninitStorage<T,N,G,Init=Self>;

    //Add TrustedLen when stabilized
    type Iter: Iterator<Item=T> + DoubleEndedIterator + ExactSizeIterator + FusedIterator;

    fn elements(&self) -> usize;

    fn dim(&self) -> N;
    fn grade(&self) -> G;

    fn uninit(n:N, g:G) -> Self::Uninit;

    fn from_iterator<I:IntoIterator<Item=T>>(n:N, g:G, iter: I) -> Self;

}

pub unsafe trait UninitStorage<T, N:Dim, G:Dim>: Storage<MaybeUninit<T>,N,G> {
    type Init: Storage<T,N,G,Uninit=Self>;
    unsafe fn assume_init(self) -> Self::Init;
}

unsafe impl<T, N:DimName, G:DimName, const L: usize> Storage<T, N, G> for [T;L] {
    type Uninit = [MaybeUninit<T>; L];
    type Iter = <Self as IntoIterator>::IntoIter;

    fn elements(&self) -> usize { L }

    fn dim(&self) -> N { N::name() }
    fn grade(&self) -> G { G::name() }

    fn uninit(_:N, _:G) -> Self::Uninit {
        //TODO: use `MaybeUninit::uninit_array()` when stabilized
        unsafe {
            //the outer MaybeUninit wraps the [MaybeUninit<T>; L] array
            MaybeUninit::uninit().assume_init()
        }
    }

    fn from_iterator<I:IntoIterator<Item=T>>(n:N, g:G, iter: I) -> Self {

        let mut uninit = Self::uninit(n,g);

        let mut count = 0;
        for (i, x) in (0..L).zip(iter) {
            uninit[i] = MaybeUninit::new(x);
            count = i;
        }

        if count+1!=L {
            panic!("Not enough elements to fill blade");
        }

        unsafe { <Self::Uninit as UninitStorage<T,N,G>>::assume_init(uninit) }

    }

}

unsafe impl<T, N:DimName, G:DimName, const L: usize> UninitStorage<T, N, G> for [MaybeUninit<T>;L] {
    type Init = [T; L];
    unsafe fn assume_init(self) -> Self::Init {
        //TODO: use `MaybeUninit::assume_init_array(self)` when stabilized
        //This _probably_ optimizes to zero-cost, but who knows!
        transmute_copy::<Self, Self::Init>(&self)
    }
}

unsafe impl<T, N:DimName, G:DimName> Storage<T, N, G> for Vec<T> {
    type Uninit = Vec<MaybeUninit<T>>;
    type Iter = <Self as IntoIterator>::IntoIter;

    fn elements(&self) -> usize { self.len() }

    fn dim(&self) -> N { N::name() }
    fn grade(&self) -> G { G::name() }

    fn uninit(n:N, g:G) -> Self::Uninit {
        let l = binom(n.value(), g.value());
        let mut vec = Vec::with_capacity(l);
        unsafe { vec.set_len(l) };
        vec
    }

    fn from_iterator<I:IntoIterator<Item=T>>(n:N, g:G, iter: I) -> Self {
        let count = binom(n.value(), g.value());
        let vec: Vec<T> = FromIterator::from_iter(iter.into_iter().take(count));
        if vec.len() != count {
            panic!("Not enough elements to fill blade");
        }
        vec
    }
}

unsafe impl<T, N:DimName, G:DimName> UninitStorage<T, N, G> for Vec<MaybeUninit<T>> {
    type Init = Vec<T>;
    unsafe fn assume_init(self) -> Self::Init {
        //TODO: maybe find something less ugly?
        transmute(self)
    }
}

#[derive(Clone)]
pub struct DynStorage<T,N:Dim,G:Dim> {
    data: Vec<T>,
    dim: N,
    grade: G
}

impl<T,N:Dim,G:Dim> Index<usize> for DynStorage<T,N,G> {
    type Output = T;
    fn index(&self, i: usize) -> &T { &self.data[i] }
}

impl<T,N:Dim,G:Dim> IndexMut<usize> for DynStorage<T,N,G> {
    fn index_mut(&mut self, i: usize) -> &mut T { &mut self.data[i] }
}

impl<T,N:Dim,G:Dim> AsRef<[T]> for DynStorage<T,N,G> {
    fn as_ref(&self) -> &[T] { self.data.as_ref() }
}

impl<T,N:Dim,G:Dim> AsMut<[T]> for DynStorage<T,N,G> {
    fn as_mut(&mut self) -> &mut [T] { self.data.as_mut() }
}

impl<T,N:Dim,G:Dim> Borrow<[T]> for DynStorage<T,N,G> {
    fn borrow(&self) -> &[T] { self.data.borrow() }
}

impl<T,N:Dim,G:Dim> BorrowMut<[T]> for DynStorage<T,N,G> {
    fn borrow_mut(&mut self) -> &mut [T] { self.data.borrow_mut() }
}

impl<T,N:Dim,G:Dim> IntoIterator for DynStorage<T,N,G> {
    type Item = T;
    type IntoIter = std::vec::IntoIter<T>;
    fn into_iter(self) -> Self::IntoIter {
        self.data.into_iter()
    }
}

unsafe impl<T,N:Dim,G:Dim> Storage<T,N,G> for DynStorage<T,N,G> {
    type Uninit = DynStorage<MaybeUninit<T>, N, G>;
    type Iter = <Self as IntoIterator>::IntoIter;

    fn elements(&self) -> usize { self.data.len() }

    fn dim(&self) -> N { self.dim }
    fn grade(&self) -> G { self.grade }

    fn uninit(n:N, g:G) -> Self::Uninit {

        //make the vec the right size
        let l = binom(n.value(), g.value());
        let mut vec = Vec::with_capacity(l);
        unsafe { vec.set_len(l) };

        //make the storage
        DynStorage {
            data: vec,
            dim: n,
            grade: g
        }
    }

    fn from_iterator<I:IntoIterator<Item=T>>(n:N, g:G, iter: I) -> Self {
        let count = binom(n.value(), g.value());
        let vec: Vec<T> = FromIterator::from_iter(iter.into_iter().take(count));
        if vec.len() != count {
            panic!("Not enough elements to fill blade");
        }
        DynStorage {
            data: vec,
            dim: n,
            grade: g
        }
    }

}

unsafe impl<T,N:Dim,G:Dim> UninitStorage<T,N,G> for DynStorage<MaybeUninit<T>,N,G> {
    type Init = DynStorage<T, N, G>;

    unsafe fn assume_init(self) -> Self::Init {
        //TODO: maybe make less ugly
        DynStorage { data: transmute(self.data), dim: self.dim, grade: self.grade }
    }

}
