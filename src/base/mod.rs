
use std::convert::{AsRef, AsMut, TryInto};
use std::borrow::{Borrow, BorrowMut};
use std::hash::{Hash, Hasher};
use std::iter::{repeat, repeat_with};
use std::mem::{MaybeUninit, transmute, transmute_copy};
use std::fmt::{
    Debug, Display, Binary, Octal, LowerHex, UpperHex, LowerExp, UpperExp,
    Formatter, Result as FmtResult
};
use std::ops::{
    Index, IndexMut,
    Deref, DerefMut,
    Add, AddAssign, Sub, SubAssign, Neg,
    Mul, MulAssign, Div, DivAssign, BitXor, Rem
};
use std::iter::{
    IntoIterator, FromIterator,
    DoubleEndedIterator, ExactSizeIterator, FusedIterator,
    //TrustedLen
};

use num_traits::{Zero, One};

use na::{ClosedAdd, ClosedSub, ComplexField};
use na::dimension::{
    Dim, DimAdd, DimSum, DimSub, DimDiff, DimNameDiff,
    Dynamic, Const, U0, U1, U2, U3, U4, U5, U6
};

use crate::basis_blade::BasisBlade;
use crate::{
    DimName, RefMul,
    binom, even_elements, odd_elements,
    components_of, even_components_of, odd_components_of
};

pub type Iter<'a, T> = std::slice::Iter<'a, T>;
pub type IterMut<'a, T> = std::slice::IterMut<'a, T>;

#[repr(transparent)]
pub struct Blade<T:AllocBlade<N,G>, N:Dim, G:Dim> {
    pub data: AllocateBlade<T,N,G>
}

#[repr(transparent)]
pub struct Even<T:AllocEven<N>, N:Dim> {
    pub data: AllocateEven<T,N>
}

#[repr(transparent)]
pub struct Odd<T:AllocOdd<N>, N:Dim> {
    pub data: AllocateOdd<T,N>
}

#[repr(transparent)]
pub struct Multivector<T:AllocMultivector<N>, N:Dim> {
    pub data: AllocateMultivector<T,N>
}

use self::storage::*;
use self::alloc::*;

pub mod storage;
pub mod alloc;
pub mod coordinates;

pub use self::common::*;
pub use self::involute::*;
pub use self::ops::*;
pub use self::mul::*;
pub use self::dual::*;
pub use self::dim_cast::*;
pub use self::constructors::*;
pub use self::aliases::*;
pub use self::fmt::*;

mod common;
mod involute;
mod ops;
mod mul;
mod dual;
mod dim_cast;
mod constructors;
mod aliases;
mod fmt;
