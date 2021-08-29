
use std::borrow::{Borrow, BorrowMut};
use std::convert::{AsRef, AsMut};
use std::iter::IntoIterator;
use std::cmp::{PartialEq, Eq};
use std::hash::{Hash, Hasher};
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

use num_traits::{Zero, One, Inv};

use na::{ClosedAdd, ClosedSub};

use crate::{RefMul, Scale, InvScale, AddGroup};
use crate::algebra::{Blade, Even, Odd, mul_selected};
use crate::base::alloc::{AllocBlade, AllocEven, AllocOdd, AllocVersor};
use crate::base::dim::{
    Dim, DimName, ToTypenum,
    DimDiff, DimNameDiff,
    DimAdd, DimSum, DimSymSub, DimSymDiff,
    Dynamic, U0, U1, U2, U3, U4, U5, U6
};


pub type Iter<'a, T> = std::slice::Iter<'a, T>;
pub type IterMut<'a, T> = std::slice::IterMut<'a, T>;

#[repr(transparent)]
#[derive(Derivative)]
#[derivative(Copy(bound = "T:Copy, Blade<T,N,G>:Copy"))]
#[derivative(Clone(bound = "T:Clone"))]
#[derivative(Hash(bound = "T:Hash"))]
pub struct SimpleBlade<T:AllocBlade<N,G>,N:Dim,G:Dim> {
    data: Blade<T,N,G>
}

#[repr(transparent)]
#[derive(Derivative)]
#[derivative(Copy(bound = "T:Copy, Blade<T,N,G>:Copy"))]
#[derivative(Clone(bound = "T:Clone"))]
#[derivative(Hash(bound = "T:Hash"))]
pub struct UnitBlade<T:AllocBlade<N,G>,N:Dim,G:Dim> {
    data: Blade<T,N,G>
}

#[repr(transparent)]
#[derive(Derivative)]
#[derivative(Copy(bound = "T:Copy, Even<T,N>:Copy"))]
#[derivative(Clone(bound = "T:Clone"))]
#[derivative(Hash(bound = "T:Hash"))]
pub struct Rotor<T:AllocEven<N>,N:Dim> {
    data: Even<T,N>
}

#[repr(transparent)]
#[derive(Derivative)]
#[derivative(Copy(bound = "T:Copy, Odd<T,N>:Copy"))]
#[derivative(Clone(bound = "T:Clone"))]
#[derivative(Hash(bound = "T:Hash"))]
pub struct Reflector<T:AllocOdd<N>,N:Dim> {
    data: Odd<T,N>
}

#[derive(Derivative)]
#[derivative(Copy(bound = "T:Copy, Rotor<T,N>:Copy, Reflector<T,N>:Copy"))]
#[derivative(Clone(bound = "T:Clone"))]
#[derivative(Hash(bound = "T:Hash"))]
pub enum Versor<T:AllocVersor<N>, N:Dim> {
    Even(Rotor<T,N>),
    Odd(Reflector<T,N>)
}

pub use self::common::*;
pub use self::mutable::*;
pub use self::involute::*;
pub use self::ops::*;
pub use self::aliases::*;
pub use self::constructors::*;

mod common;
mod mutable;
mod involute;
mod ops;
mod aliases;
mod constructors;
