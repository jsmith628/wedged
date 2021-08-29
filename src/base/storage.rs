
use std::borrow::{Borrow, BorrowMut};
use std::ops::{Index, IndexMut};
use std::convert::{AsRef, AsMut, TryInto};
use std::iter::{IntoIterator, FromIterator, FusedIterator};
use std::mem::{MaybeUninit, transmute, transmute_copy};

use crate::binom;

use na::dimension::{Dim};

pub unsafe trait Storage<T>:
    Index<usize, Output=T> + IndexMut<usize> +
    AsRef<[T]> + AsMut<[T]> +
    Borrow<[T]> + BorrowMut<[T]> +
    IntoIterator<Item=T, IntoIter=Self::Iter>
{
    type Uninit: UninitStorage<T,Init=Self>;

    //Add TrustedLen when stabilized
    type Iter: Iterator<Item=T> + DoubleEndedIterator + ExactSizeIterator + FusedIterator;

    fn elements(&self) -> usize;

    //so that we don't have to have Allocate<Self>: Clone bounds
    fn clone_storage(&self) -> Self where T:Clone;
    fn clone_from_storage(&mut self, other: &Self) where T:Clone;


}

pub unsafe trait UninitStorage<T>: Storage<MaybeUninit<T>> {
    type Init: Storage<T,Uninit=Self>;
    unsafe fn assume_init(self) -> Self::Init;
}

pub unsafe trait BladeStorage<T,N:Dim,G:Dim>: Storage<T> {

    fn dim(&self) -> N;
    fn grade(&self) -> G;

    fn uninit(n:N, g:G) -> Self::Uninit;
    fn from_iterator<I:IntoIterator<Item=T>>(n:N, g:G, iter: I) -> Self;

}

pub unsafe trait EvenStorage<T,N:Dim>: Storage<T> {
    fn dim(&self) -> N;
    fn uninit(n:N) -> Self::Uninit;
    fn from_iterator<I:IntoIterator<Item=T>>(n:N, iter: I) -> Self;
}

pub unsafe trait OddStorage<T,N:Dim>: Storage<T> {
    fn dim(&self) -> N;
    fn uninit(n:N) -> Self::Uninit;
    fn from_iterator<I:IntoIterator<Item=T>>(n:N, iter: I) -> Self;
}

pub unsafe trait MultivectorStorage<T,N:Dim>: Storage<T> {
    fn dim(&self) -> N;
    fn uninit(n:N) -> Self::Uninit;
    fn from_iterator<I:IntoIterator<Item=T>>(n:N, iter: I) -> Self;
}

unsafe impl<T, const L: usize> Storage<T> for [T;L] {
    type Uninit = [MaybeUninit<T>; L];
    type Iter = <Self as IntoIterator>::IntoIter;
    fn elements(&self) -> usize { L }
    fn clone_storage(&self) -> Self where T:Clone { self.clone() }
    fn clone_from_storage(&mut self, other: &Self) where T:Clone { self.clone_from(other) }
}

unsafe impl<T, const L: usize> UninitStorage<T> for [MaybeUninit<T>;L] {
    type Init = [T; L];
    unsafe fn assume_init(self) -> Self::Init {
        //TODO: use `MaybeUninit::assume_init_array(self)` when stabilized
        //This _probably_ optimizes to zero-cost, but who knows!
        transmute_copy::<Self, Self::Init>(&self)
    }
}

#[inline(always)]
fn vec_uninit<T>(count:usize) -> Vec<MaybeUninit<T>> {
    let mut vec = Vec::with_capacity(count);
    unsafe { vec.set_len(count) };
    vec
}

#[inline(always)]
fn vec_from_iter<T,I:IntoIterator<Item=T>>(count:usize, iter: I, kind:&str) -> Vec<T> {
    let vec: Vec<T> = FromIterator::from_iter(iter.into_iter().take(count));
    if vec.len() != count {
        panic!("Not enough elements to fill {}", kind);
    }
    vec
}

#[derive(Clone)]
pub struct DynBladeStorage<T,N:Dim,G:Dim> {
    data: Vec<T>,
    dim: N,
    grade: G
}

#[derive(Clone)]
pub struct DynEvenStorage<T,N:Dim> {
    data: Vec<T>,
    dim: N
}

#[derive(Clone)]
pub struct DynOddStorage<T,N:Dim> {
    data: Vec<T>,
    dim: N
}

#[derive(Clone)]
pub struct DynMultivectorStorage<T,N:Dim> {
    data: Vec<T>,
    dim: N
}

macro_rules! impl_dyn_storage {
    ($($Ty:ident<T, $($N:ident),*>;)*) => {
        $(
            impl<T,$($N:Dim),*> Index<usize> for $Ty<T,$($N),*> {
                type Output = T;
                fn index(&self, i: usize) -> &T { &self.data[i] }
            }

            impl<T,$($N:Dim),*> IndexMut<usize> for $Ty<T,$($N),*> {
                fn index_mut(&mut self, i: usize) -> &mut T { &mut self.data[i] }
            }

            impl<T,$($N:Dim),*> AsRef<[T]> for $Ty<T,$($N),*> {
                fn as_ref(&self) -> &[T] { self.data.as_ref() }
            }

            impl<T,$($N:Dim),*> AsMut<[T]> for $Ty<T,$($N),*> {
                fn as_mut(&mut self) -> &mut [T] { self.data.as_mut() }
            }

            impl<T,$($N:Dim),*> Borrow<[T]> for $Ty<T,$($N),*> {
                fn borrow(&self) -> &[T] { self.data.borrow() }
            }

            impl<T,$($N:Dim),*> BorrowMut<[T]> for $Ty<T,$($N),*> {
                fn borrow_mut(&mut self) -> &mut [T] { self.data.borrow_mut() }
            }

            impl<T,$($N:Dim),*> IntoIterator for $Ty<T,$($N),*> {
                type Item = T;
                type IntoIter = std::vec::IntoIter<T>;
                fn into_iter(self) -> Self::IntoIter {
                    self.data.into_iter()
                }
            }

            unsafe impl<T,$($N:Dim),*> Storage<T> for $Ty<T,$($N),*> {
                type Uninit = $Ty<MaybeUninit<T>,$($N),*>;
                type Iter = <Self as IntoIterator>::IntoIter;
                fn elements(&self) -> usize { self.data.len() }
                fn clone_storage(&self) -> Self where T:Clone { self.clone() }
                fn clone_from_storage(&mut self, other: &Self) where T:Clone { self.clone_from(other) }
            }

        )*
    }
}

impl_dyn_storage!(
    DynBladeStorage<T,N,G>; DynEvenStorage<T,N>; DynOddStorage<T,N>; DynMultivectorStorage<T,N>;
);

unsafe impl<T,N:Dim,G:Dim> UninitStorage<T> for DynBladeStorage<MaybeUninit<T>,N,G> {
    type Init = DynBladeStorage<T,N,G>;

    unsafe fn assume_init(self) -> Self::Init {
        //TODO: maybe make less ugly
        DynBladeStorage { data: transmute(self.data), dim: self.dim, grade: self.grade }
    }

}

unsafe impl<T,N:Dim,G:Dim> BladeStorage<T,N,G> for DynBladeStorage<T,N,G> {

    fn dim(&self) -> N { self.dim }
    fn grade(&self) -> G { self.grade }

    fn uninit(n:N, g:G) -> Self::Uninit {
        DynBladeStorage {
            data: vec_uninit(binom(n.value(), g.value())),
            dim: n,
            grade: g
        }
    }

    fn from_iterator<I:IntoIterator<Item=T>>(n:N, g:G, iter: I) -> Self {
        DynBladeStorage {
            data: vec_from_iter(binom(n.value(), g.value()), iter, "blade"),
            dim: n,
            grade: g
        }
    }

}

#[inline(always)]
fn even_elements(n:usize) -> usize {
    crate::even_elements(n.try_into().unwrap())
}

unsafe impl<T,N:Dim> UninitStorage<T> for DynEvenStorage<MaybeUninit<T>,N> {
    type Init = DynEvenStorage<T,N>;

    unsafe fn assume_init(self) -> Self::Init {
        //TODO: maybe make less ugly
        DynEvenStorage { data: transmute(self.data), dim: self.dim }
    }

}

unsafe impl<T,N:Dim> EvenStorage<T,N> for DynEvenStorage<T,N> {

    fn dim(&self) -> N { self.dim }

    fn uninit(n:N) -> Self::Uninit {
        DynEvenStorage {
            data: vec_uninit(even_elements(n.value())),
            dim: n
        }
    }

    fn from_iterator<I:IntoIterator<Item=T>>(n:N, iter: I) -> Self {
        DynEvenStorage {
            data: vec_from_iter(even_elements(n.value()), iter, "value"),
            dim: n
        }
    }

}

#[inline(always)]
fn odd_elements(n:usize) -> usize {
    crate::odd_elements(n.try_into().unwrap())
}

unsafe impl<T,N:Dim> UninitStorage<T> for DynOddStorage<MaybeUninit<T>,N> {
    type Init = DynOddStorage<T,N>;

    unsafe fn assume_init(self) -> Self::Init {
        //TODO: maybe make less ugly
        DynOddStorage { data: transmute(self.data), dim: self.dim }
    }

}

unsafe impl<T,N:Dim> OddStorage<T,N> for DynOddStorage<T,N> {

    fn dim(&self) -> N { self.dim }

    fn uninit(n:N) -> Self::Uninit {
        DynOddStorage {
            data: vec_uninit(odd_elements(n.value())),
            dim: n
        }
    }

    fn from_iterator<I:IntoIterator<Item=T>>(n:N, iter: I) -> Self {
        DynOddStorage {
            data: vec_from_iter(odd_elements(n.value()), iter, "value"),
            dim: n
        }
    }

}


unsafe impl<T,N:Dim> UninitStorage<T> for DynMultivectorStorage<MaybeUninit<T>,N> {
    type Init = DynMultivectorStorage<T,N>;

    unsafe fn assume_init(self) -> Self::Init {
        //TODO: maybe make less ugly
        DynMultivectorStorage { data: transmute(self.data), dim: self.dim }
    }

}

#[inline(always)]
fn multivector_elements(n:usize) -> usize {
    2_usize.pow(n.try_into().unwrap())
}

unsafe impl<T,N:Dim> MultivectorStorage<T,N> for DynMultivectorStorage<T,N> {

    fn dim(&self) -> N { self.dim }

    fn uninit(n:N) -> Self::Uninit {
        DynMultivectorStorage {
            data: vec_uninit(multivector_elements(n.value())),
            dim: n
        }
    }

    fn from_iterator<I:IntoIterator<Item=T>>(n:N, iter: I) -> Self {
        DynMultivectorStorage {
            data: vec_from_iter(multivector_elements(n.value()), iter, "multivector"),
            dim: n
        }
    }

}
