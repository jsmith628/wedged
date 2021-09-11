
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
use std::iter::IntoIterator;

use num_traits::{Zero, One};

use na::ComplexField;

use crate::base::storage::*;
use crate::base::alloc::*;
use crate::base::dim::{
    Dim, DimName, DimAdd, DimSum, DimSub, DimDiff, DimNameDiff, DimSymSub, DimSymDiff,
    Dynamic, U0, U1, U2, U3, U4, U5, U6
};

use crate::basis_blade::BasisBlade;
use crate::{
    RefMul, Scale, InvScale, AddGroup,
    binom, components_of, even_components_of, odd_components_of,
    grade_index_in_versor, grade_index_in_multivector
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

pub use self::common::*;
pub use self::involute::*;
pub use self::ops::*;
pub use self::mul::*;
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
mod dual;
mod dim_cast;
mod grade_cast;
mod constructors;
mod aliases;
mod fmt;
