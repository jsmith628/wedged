//!
//! Traits and structs for the storage of vector-like data.
//!
//! The purpose of this module is to provide a system that unifies the different statically-sized
//! arrays and dynamic arrays (like vec) in order to make managing the backing data of the algebras
//! easier. Since the data in the algebra structs are given generically from
//! [`Alloc`], we need a trait to bound that associated type that provides all
//! the functionality we need.
//!

use std::borrow::{Borrow, BorrowMut};
use std::ops::{Index, IndexMut};
use std::convert::{AsRef, AsMut};
use std::iter::{IntoIterator, FromIterator, FusedIterator};
use std::mem::{MaybeUninit, transmute, transmute_copy};

#[cfg(doc)] use crate::base::dim::*;
#[cfg(doc)] use crate::base::alloc::*;
#[cfg(doc)] use crate::algebra::*;

use crate::base::count::*;

use na::dimension::{Dim};

/// Contains all the array-like functionality we need for backing buffers for the algebraic types
pub unsafe trait Storage<T>:
    Index<usize, Output=T> + IndexMut<usize> +
    AsRef<[T]> + AsMut<[T]> +
    Borrow<[T]> + BorrowMut<[T]> +
    IntoIterator<Item=T, IntoIter=Self::Iter>
{

    ///The corresponding uninitialized storage that we can transmute into this type
    type Uninit: UninitStorage<T,Init=Self>;

    ///
    /// The iterator over this type. Wraps [`IntoIterator::IntoIter`]
    ///
    /// We need this so we can add extra trait bounds to the `IntoIterator::IntoIter`
    /// implementation for `Self`.
    type Iter: Iterator<Item=T> + DoubleEndedIterator + ExactSizeIterator + FusedIterator; //Add TrustedLen when stabilized

    ///
    /// The number of items in self.
    ///
    /// Note this takes in `&self` and can vary over time so that we can support [`Dynamic`] dimensions
    fn elements(&self) -> usize;

    ///
    /// Wraps [`Clone::clone()`] whenever `T:Clone`
    ///
    /// This allows us to have `Clone` `impl`s that only require `T:Clone` and no bounds on
    /// the underlying storage object.
    fn clone_storage(&self) -> Self where T:Clone;

    ///
    /// Wraps [`Clone::clone_from()`] whenever `T:Clone`
    ///
    /// This allows us to have `Clone` `impl`s that only require `T:Clone` and no bounds on
    /// the underlying storage object.
    fn clone_from_storage(&mut self, other: &Self) where T:Clone;


}

///
/// A [`Storage`] type that contains [`MaybeUninit<T>`] elements.
///
/// This allows us to follow the  [`std::mem::MaybeUninit`] design when constructing the algebraic
/// structs and still have access to individual elements of the buffer
pub unsafe trait UninitStorage<T>: Storage<MaybeUninit<T>> {
    /// The initialized storage that we can trasmute this type into
    type Init: Storage<T,Uninit=Self>;

    ///
    /// Transmutes this buffer into one assumed to be initialized
    ///
    /// # Safety
    /// Should follow all design considerations of [`MaybeUninit::assume_init()`]
    unsafe fn assume_init(self) -> Self::Init;
}

/// A [`Storage`] type that can contain a [`Blade`] of the given dimension and grade
pub unsafe trait BladeStorage<T,N:Dim,G:Dim>: Storage<T> {

    ///The dimension of `Blade` being stored. Can vary when using a [`Dynamic`] dimension
    fn dim(&self) -> N;

    ///The dimension of `Blade` being stored. Can vary when using a [`Dynamic`] grade
    fn grade(&self) -> G;

    ///Allocates a buffer to contain a `Blade` of the given dimension and grade
    fn uninit(n:N, g:G) -> Self::Uninit;

    ///Allocates and initializes a buffer to contain a `Blade` of the given dimension and grade
    fn from_iterator<I:IntoIterator<Item=T>>(n:N, g:G, iter: I) -> Self;

}

/// A [`Storage`] type that can contain an [`Even`] of the given dimension
pub unsafe trait EvenStorage<T,N:Dim>: Storage<T> {

    ///The dimension of `Even` being stored. Can vary when using a [`Dynamic`] dimension
    fn dim(&self) -> N;

    ///Allocates a buffer to contain a `Even` of the given dimension
    fn uninit(n:N) -> Self::Uninit;

    ///Allocates and initializes a buffer to contain a `Even` of the given dimension
    fn from_iterator<I:IntoIterator<Item=T>>(n:N, iter: I) -> Self;
}

/// A [`Storage`] type that can contain an [`Odd`] of the given dimension
pub unsafe trait OddStorage<T,N:Dim>: Storage<T> {

    ///The dimension of `Odd` being stored. Can vary when using a [`Dynamic`] dimension
    fn dim(&self) -> N;

    ///Allocates a buffer to contain a `Odd` of the given dimension
    fn uninit(n:N) -> Self::Uninit;

    ///Allocates and initializes a buffer to contain a `Odd` of the given dimension
    fn from_iterator<I:IntoIterator<Item=T>>(n:N, iter: I) -> Self;
}

/// A [`Storage`] type that can contain a [`Multivector`] of the given dimension
pub unsafe trait MultivectorStorage<T,N:Dim>: Storage<T> {

    ///The dimension of `Multivector` being stored. Can vary when using a [`Dynamic`] dimension
    fn dim(&self) -> N;

    ///Allocates a buffer to contain a `Multivector` of the given dimension
    fn uninit(n:N) -> Self::Uninit;

    ///Allocates and initializes a buffer to contain a `Multivector` of the given dimension
    fn from_iterator<I:IntoIterator<Item=T>>(n:N, iter: I) -> Self;
}

//
//Statically sized arrays
//

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

//
// Dynamic storage
//

#[inline(always)]
fn vec_uninit<T>(count:usize) -> Vec<MaybeUninit<T>> {
    //Ideally, there'd be a built-in function for this, but it *does* work within the guarrantees
    //made by a Vec, so we're gonna do it anyway!
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

/// Storage buffer for a [`Blade`] that can use a
/// [`Dynamic`] dim to vary its size at runtime
#[derive(Clone)]
pub struct DynBladeStorage<T,N:Dim,G:Dim> {
    data: Vec<T>,
    dim: N,
    grade: G
}

/// Storage buffer for an [`Even`] that can use a
/// [`Dynamic`] dim to vary its size at runtime
#[derive(Clone)]
pub struct DynEvenStorage<T,N:Dim> {
    data: Vec<T>,
    dim: N
}

/// Storage buffer for an [`Odd`] that can use a
/// [`Dynamic`] dim to vary its size at runtime
#[derive(Clone)]
pub struct DynOddStorage<T,N:Dim> {
    data: Vec<T>,
    dim: N
}

/// Storage buffer for a [`Multivector`] that can use a
/// [`Dynamic`] dim to vary its size at runtime
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
