//!
//! Structs for interpreting geometric algebra as vector spaces and orthogonal transformations
//!
//! This module aims to streamline the use of the algebra for geometric uses by adding additional
//! constraints onto the types from [`galgebra::algebra`]. This is accomplished by wrapping the
//! algebraic types in additional structs where the allowed operations are much more limited.
//!
//! For example, in order to preserve the fact it represents a rotation, a [`Rotor`] cannot be
//! added to another `Rotor`, and to preserve its unit length, a [`UnitBlade`] cannot be multiplied
//! by a scalar.
//!
//! # Organization
//!
//!  To this aim, there are five main structs in this module:
//! - [`SimpleBlade`]: A [`Blade`] that is guarranteed to be the wedge product of vectors.
//! - [`UnitBlade`]: A [`SimpleBlade`] guarranteed to have a length of 1
//! - [`Rotor`]: An [`Even`] representing a rotation
//! - [`Reflector`]: An [`Odd`] representing a reflection combined with a possible rotation
//! - [`Versor`]: An [`Even`] *or* [`Odd`] representing a general orthogonal transformation
//!
//!

use std::borrow::{Borrow, BorrowMut};
use std::convert::{AsRef, AsMut};
use std::iter::{IntoIterator, FromIterator, Sum, Product};
use std::cmp::{PartialEq, Eq};
use std::hash::Hash;
use std::ops::{
    Index, IndexMut,
    Deref, DerefMut,
    Add, AddAssign, Sub, SubAssign, Neg,
    Mul, MulAssign, Div, DivAssign, Rem, BitXor
};
use std::fmt::{
    Formatter, Result as FmtResult,
    Debug, Display, Binary, Octal, LowerHex, UpperHex, LowerExp, UpperExp
};

use approx::{AbsDiffEq, RelativeEq, UlpsEq};
use num_traits::{Zero, One, Inv};
use typenum::{True, IsLessOrEqual};

use crate::base::*;
use crate::algebra::*;

// #[cfg(test)] use crate::TEST_DIM;

pub type Iter<'a, T> = std::slice::Iter<'a, T>;
pub type IterMut<'a, T> = std::slice::IterMut<'a, T>;

///
/// A [`Blade`] that is the wedge product of `G` vectors
///
/// This is usually used to represent weighted vector spaces or when the cost to normalize to
/// a [`UnitBlade`] is too high.
///
#[repr(transparent)]
#[derive(Derivative)]
#[derivative(Copy(bound = "T:Copy, Blade<T,N,G>:Copy"))]
#[derivative(Clone(bound = "T:Clone"))]
#[derivative(Hash(bound = "T:Hash"))]
pub struct SimpleBlade<T:AllocBlade<N,G>,N:Dim,G:Dim> {
    data: Blade<T,N,G>
}

///
/// A [`SimpleBlade`] with unit length
///
/// Primary use is to represent oriented vector spaces of dimension `G`. If the quantity is going
/// to be stored/cached for an extended period of time, this can also provide an optimization over
/// a `SimpleBlade` since the length does not have to be accounted for.
///
#[repr(transparent)]
#[derive(Derivative)]
#[derivative(Copy(bound = "T:Copy, Blade<T,N,G>:Copy"))]
#[derivative(Clone(bound = "T:Clone"))]
#[derivative(Hash(bound = "T:Hash"))]
pub struct UnitBlade<T:AllocBlade<N,G>,N:Dim,G:Dim> {
    data: Blade<T,N,G>
}

/// Represents a rotation in `N` dimensions
#[repr(transparent)]
#[derive(Derivative)]
#[derivative(Copy(bound = "T:Copy, Even<T,N>:Copy"))]
#[derivative(Clone(bound = "T:Clone"))]
#[derivative(Hash(bound = "T:Hash"))]
pub struct Rotor<T:AllocEven<N>,N:Dim> {
    data: Even<T,N>
}

/// Represents a reflection in `N` dimensions (with an optional rotation component)
#[repr(transparent)]
#[derive(Derivative)]
#[derivative(Copy(bound = "T:Copy, Odd<T,N>:Copy"))]
#[derivative(Clone(bound = "T:Clone"))]
#[derivative(Hash(bound = "T:Hash"))]
pub struct Reflector<T:AllocOdd<N>,N:Dim> {
    data: Odd<T,N>
}

/// A general orthogonal transformation in `N` dimensions
#[derive(Derivative)]
#[derivative(Copy(bound = "T:Copy, Rotor<T,N>:Copy, Reflector<T,N>:Copy"))]
#[derivative(Clone(bound = "T:Clone"))]
#[derivative(Hash(bound = "T:Hash"))]
pub enum Versor<T:AllocVersor<N>, N:Dim> {
    Even(Rotor<T,N>),
    Odd(Reflector<T,N>)
}

macro_rules! maybe_ref {
    ($e:expr; ) => { $e };
    ($e:expr; $a:lifetime) => { &$e };
}

pub use self::common::*;
pub use self::mutable::*;
pub use self::involute::*;
pub use self::ops::*;
pub use self::blade::*;
pub use self::versor::*;
pub use self::aliases::*;
pub use self::constructors::*;

mod common;
mod mutable;
mod involute;
mod ops;
mod blade;
mod versor;
mod cast;
mod aliases;
mod constructors;
