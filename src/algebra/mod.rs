//!
//! Contains the structs for the core algebra
//!
//! # Design
//!
//! Everything in this module is implemented purely algebraically and is maximally
//! permittive of which operations are implemented and allowed.
//!
//! In particular, this means that every struct in this module allows for things like direct
//! mutation of elements, addition/subtraction, permittive casting, etc. However, this also means
//! that the structs have less guarrantees about certain properties.
//!
//! In particular:
//! - not every [`Blade`] is necessarily the wedge of two vectors and doesn't necessarily represent
//!   a vector space, as you can potentially add together two mutually orthogonal blades together.
//! - not every [`Even`] represents a rotation, as not all of them have unit length or have a purely
//!   rotational action
//!
//! # Organization
//!
//! This module is split between four different types, each representing a different subset of the
//! broader algebra:
//! - [`Multivector`]: represents a general element in the algebra
//! - [`Even`]: represents an element with components of even grade
//! - [`Odd`]: represents an element with components of odd grade
//! - [`Blade`]: represents an element with components of odd grade
//!
//! # Use case
//!
//! The primary use purpose of this module is to provide the core algebra for the
//! geometric interpretations and modules, but there are a few important additional use cases.
//!
//! For example:
//! - Certain physical quantities. In particular, position, velocity, angular velocity,
//!   angular momentum, etc are all best represented using [`VecN`]s and [`BiVecN`]s since
//!   each of those require addition.
//! - [`Even2`] and [`Even3`] are isomorphic to complex numbers and quaternions respectively
//! - Certain reinterpretations of Maxwell's Equations use a [`Multivector`] to represent
//!   the electromagnetic field.
//!

use std::convert::{AsRef, AsMut};
use std::borrow::{Borrow, BorrowMut};
use std::hash::{Hash, Hasher};
use std::iter::{once_with, repeat, repeat_with};
use std::mem::MaybeUninit;
use std::fmt::{
    Debug, Display, Binary, Octal, LowerHex, UpperHex, LowerExp, UpperExp,
    Formatter, Result as FmtResult
};
use std::ops::{
    Index, IndexMut,
    Add, AddAssign, Sub, SubAssign, Neg,
    Mul, MulAssign, Div, DivAssign, BitXor, Rem
};
use std::iter::{IntoIterator, FromIterator, Sum, Product};

use num_traits::{Zero, One};

use na::{ComplexField, /*RealField*/};
use approx::{AbsDiffEq, RelativeEq, UlpsEq};

#[cfg(test)] use crate::TEST_DIM;

use crate::base::*;

/// An iterator of references of each element
pub type Iter<'a, T> = std::slice::Iter<'a, T>;

/// An iterator of mutable references of each element
pub type IterMut<'a, T> = std::slice::IterMut<'a, T>;

/// A general element of a particular dimension and grade
#[repr(transparent)]
pub struct Blade<T:AllocBlade<N,G>, N:Dim, G:Dim> {
    pub data: AllocateBlade<T,N,G>
}

/// A general element with all even components in the given dimension
#[repr(transparent)]
pub struct Even<T:AllocEven<N>, N:Dim> {
    pub data: AllocateEven<T,N>
}

/// A general element with all odd components in the given dimension
#[repr(transparent)]
pub struct Odd<T:AllocOdd<N>, N:Dim> {
    pub data: AllocateOdd<T,N>
}

/// A general element in the geometric algebra in the given dimension
#[repr(transparent)]
pub struct Multivector<T:AllocMultivector<N>, N:Dim> {
    pub data: AllocateMultivector<T,N>
}

pub use self::common::*;
pub use self::involute::*;
pub use self::ops::*;
pub use self::mul::*;
// pub use self::exp::*;
pub use self::dual::*;
pub use self::dim_cast::*;
pub use self::grade_cast::*;
pub use self::constructors::*;
pub use self::aliases::*;
pub use self::fmt::*;

mod common;
mod involute;
mod ops;
mod mul;
mod exp;
mod dual;
mod dim_cast;
mod grade_cast;
mod constructors;
mod aliases;
mod fmt;
