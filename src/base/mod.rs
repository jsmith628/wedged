
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
    Add, AddAssign, Sub, SubAssign, Neg,
    Mul, MulAssign, Div, DivAssign, BitXor, Rem
};
use std::iter::{
    IntoIterator, FromIterator,
    DoubleEndedIterator, ExactSizeIterator, FusedIterator,
    //TrustedLen
};

use num_traits::{Zero, One};

use na::{ClosedAdd, ClosedSub};
use na::dimension::{
    Dim, DimAdd, DimSum, DimSub, DimDiff, DimNameDiff,
    Dynamic, Const, U0, U1, U2, U3, U4, U5, U6
};

use crate::basis_blade::BasisBlade;
use crate::{DimName, binom, rotor_elements};

pub type Iter<'a, T> = std::slice::Iter<'a, T>;
pub type IterMut<'a, T> = std::slice::IterMut<'a, T>;

pub struct Blade<T:AllocBlade<N,G>, N:Dim, G:Dim> {
    pub data: AllocateBlade<T,N,G>
}

pub struct Rotor<T:AllocRotor<N>, N:Dim> {
    pub data: AllocateRotor<T,N>
}

pub struct Multivector<T:AllocMultivector<N>, N:Dim> {
    pub data: AllocateMultivector<T,N>
}

impl<T:AllocBlade<N,G>, N:Dim, G:Dim> Blade<T,N,G> {

    pub fn dim_generic(&self) -> N { self.data.dim() }
    pub fn grade_generic(&self) -> G { self.data.grade() }

    ///
    /// The number of dimensions this blade resides in
    ///
    /// Note that this differs from both the [grade](Blade::grade) and number of
    /// [elements](Blade::elements). Instead, this describes the dimension of the vector space
    /// generating the algebra this blade resides in.
    ///
    /// # Examples
    /// ```
    /// # use galgebra::base::*;
    ///
    /// //A static and dynamic 3D vector
    /// let v1 = Vec3::new(6, 2, 8);
    /// let v2 = VecD::from_element(3, 0.0);
    ///
    /// assert_eq!(v1.dim(), 3);
    /// assert_eq!(v2.dim(), 3);
    ///
    /// //Two 4D bivectors
    /// let b1 = BiVec4::new(6, 2, 8, 3, 1, 8);
    /// let b2 = BiVecD::from_element(4, 0.0);
    ///
    /// assert_eq!(b1.dim(), 4);
    /// assert_eq!(b2.dim(), 4);
    ///
    /// ```
    ///
    pub fn dim(&self) -> usize { self.dim_generic().value() }

    ///
    /// The grade of this blade
    ///
    /// This describes the "dimension" of the vector space this blade represents. Note that this
    /// is completely different that the [dimension](Blade::dim) of the blade which describes the
    /// the dimension of the surrounding space the blade lives in.
    ///
    /// More concretely, the grade is the number of vector basis elements multiplied together
    /// to get the basis of this blade.
    ///
    /// # Examples
    /// ```
    /// # use galgebra::base::*;
    ///
    /// //All vectors are grade 1
    /// let v1 = Vec3::new(6, 2, 8);
    /// let v2 = Vec6::new(6, 2, 8, 3, 1, 8);
    /// let v3 = VecD::from_element(2, 0.0);
    ///
    /// assert_eq!(v1.grade(), 1);
    /// assert_eq!(v2.grade(), 1);
    /// assert_eq!(v3.grade(), 1);
    ///
    /// //All Bivectors are grade 2
    /// let b1 = BiVec4::new(6, 2, 8, 3, 1, 8);
    /// let b2 = BiVecD::from_element(3, 0.0);
    ///
    /// assert_eq!(b1.grade(), 2);
    /// assert_eq!(b2.grade(), 2);
    ///
    /// //Dynamic blades
    /// let blade1 = Blade6::from_element(5, 0.0);
    /// let blade2 = BladeD::from_element(4, 3, 0.0);
    ///
    /// assert_eq!(blade1.grade(), 5);
    /// assert_eq!(blade2.grade(), 3);
    ///
    /// ```
    ///
    pub fn grade(&self) -> usize { self.grade_generic().value() }

    ///
    /// The number of elements in this blade
    ///
    /// Note that this is _not_ equal to either the [dimension](Blade::dim) and
    /// [grade](Blade::grade) of this blade. Rather, the number of elements should instead be
    /// equal to [`binom(self.dim(), self.grade())`](crate::binom) (though the value is cached
    /// and one should not worry about unnecessary computation)
    ///
    /// # Examples
    /// ```
    /// # use galgebra::base::*;
    ///
    /// let v1 = Vec6::new(6, 2, 8, 3, 1, 8);
    /// let v2 = VecD::from_element(2, 0.0);
    /// let b1 = BiVec3::new(6, 2, 8);
    /// let b2 = BiVecD::from_element(4, 0.0);
    ///
    /// assert_eq!(v1.elements(), 6);
    /// assert_eq!(v2.elements(), 2);
    /// assert_eq!(b1.elements(), 3);
    /// assert_eq!(b2.elements(), 6);
    ///
    /// //In general, the number of elemets is equal to `binom(b.dim(), b.grade())`
    /// use galgebra::binom;
    /// for n in 0..16 {
    ///     for g in 0..=n {
    ///         let b = BladeD::from_element(n, g, 0.0);
    ///         assert_eq!(b.elements(), binom(n, g))
    ///     }
    /// }
    ///
    /// ```
    ///
    pub fn elements(&self) -> usize { self.data.elements() }

    pub fn as_slice(&self) -> &[T] { self.data.borrow() }
    pub fn as_mut_slice(&mut self) -> &mut [T] { self.data.borrow_mut() }

    pub fn iter(&self) -> Iter<T> { self.as_slice().iter() }
    pub fn iter_mut(&mut self) -> IterMut<T> { self.as_mut_slice().iter_mut() }

}

impl<T:AllocRotor<N>,N:Dim> Rotor<T,N> {

    pub fn dim_generic(&self) -> N { self.data.dim() }

    pub fn dim(&self) -> usize { self.dim_generic().value() }
    pub fn elements(&self) -> usize { self.data.elements() }

    pub fn as_slice(&self) -> &[T] { self.data.borrow() }
    pub fn as_mut_slice(&mut self) -> &mut [T] { self.data.borrow_mut() }

    pub fn iter(&self) -> Iter<T> { self.as_slice().iter() }
    pub fn iter_mut(&mut self) -> IterMut<T> { self.as_mut_slice().iter_mut() }

}

impl<T:AllocMultivector<N>,N:Dim> Multivector<T,N> {

    pub fn dim_generic(&self) -> N { self.data.dim() }

    pub fn dim(&self) -> usize { self.dim_generic().value() }
    pub fn elements(&self) -> usize { self.data.elements() }

    pub fn as_slice(&self) -> &[T] { self.data.borrow() }
    pub fn as_mut_slice(&mut self) -> &mut [T] { self.data.borrow_mut() }

    pub fn iter(&self) -> Iter<T> { self.as_slice().iter() }
    pub fn iter_mut(&mut self) -> IterMut<T> { self.as_mut_slice().iter_mut() }

}

use self::storage::*;
use self::alloc::*;

pub mod storage;
pub mod alloc;

pub use self::ops::*;
pub use self::mul::*;
pub use self::constructors::*;
pub use self::aliases::*;
pub use self::fmt::*;

mod ops;
mod mul;
mod constructors;
mod aliases;
mod fmt;

macro_rules! impl_basic_traits {
    (impl<T:$Alloc:ident, $($N:ident),*> $Ty:ident where $Allocate:ident {}) => {

        impl<T:$Alloc<$($N),*>, $($N:Dim),*> Clone for $Ty<T,$($N),*> where $Allocate<T,$($N),*>: Clone {
            fn clone(&self) -> Self { $Ty { data: self.data.clone() } }
            fn clone_from(&mut self, src: &Self) { self.data.clone_from(&src.data) }
        }

        impl<T:$Alloc<$($N),*>, $($N:Dim),*> Copy for $Ty<T,$($N),*> where $Allocate<T,$($N),*>: Copy {}


        impl<T:$Alloc<$($N),*>, $($N:Dim),*> AsRef<[T]> for $Ty<T,$($N),*> {
            fn as_ref(&self) -> &[T] { self.data.as_ref() }
        }

        impl<T:$Alloc<$($N),*>, $($N:Dim),*> AsMut<[T]> for $Ty<T,$($N),*> {
            fn as_mut(&mut self) -> &mut [T] { self.data.as_mut() }
        }

        impl<T:$Alloc<$($N),*>, $($N:Dim),*> Borrow<[T]> for $Ty<T,$($N),*> {
            fn borrow(&self) -> &[T] { self.data.borrow() }
        }

        impl<T:$Alloc<$($N),*>, $($N:Dim),*> BorrowMut<[T]> for $Ty<T,$($N),*> {
            fn borrow_mut(&mut self) -> &mut [T] { self.data.borrow_mut() }
        }

        impl<T:$Alloc<$($N),*>+Eq, $($N:Dim),*> Eq for $Ty<T,$($N),*> {}

        impl<T:$Alloc<$($N),*>+Hash, $($N:Dim),*> Hash for $Ty<T,$($N),*> {
            fn hash<H:Hasher>(&self, h: &mut H) {
                T::hash_slice(self.borrow(), h)
            }
        }

        impl<T:$Alloc<$($N),*>, $($N:Dim),*> IntoIterator for $Ty<T,$($N),*> {
            type Item = T;
            type IntoIter = <$Allocate<T,$($N),*> as Storage<T>>::Iter;
            fn into_iter(self) -> Self::IntoIter {
                self.data.into_iter()
            }
        }

        impl<'a, T:$Alloc<$($N),*>, $($N:Dim),*> IntoIterator for &'a $Ty<T,$($N),*> {
            type Item = &'a T;
            type IntoIter = Iter<'a, T>;
            fn into_iter(self) -> Self::IntoIter { self.iter() }
        }

        impl<'a, T:$Alloc<$($N),*>, $($N:Dim),*> IntoIterator for &'a mut $Ty<T,$($N),*> {
            type Item = &'a mut T;
            type IntoIter = IterMut<'a, T>;
            fn into_iter(self) -> Self::IntoIter { self.iter_mut() }
        }

    }
}

impl_basic_traits!(impl<T:AllocBlade, N, G> Blade where AllocateBlade {});
impl_basic_traits!(impl<T:AllocRotor, N> Rotor where AllocateRotor {});
impl_basic_traits!(impl<T:AllocMultivector, N> Multivector where AllocateMultivector {});

impl<T, U, N1:Dim, N2:Dim, G1:Dim, G2:Dim> PartialEq<Blade<U,N2,G2>> for Blade<T,N1,G1>
where
    T: AllocBlade<N1,G1> + PartialEq<U>,
    U: AllocBlade<N2,G2>
{
    fn eq(&self, rhs:&Blade<U,N2,G2>) -> bool {
        self.dim() == rhs.dim() && self.grade() == rhs.grade() && self.as_slice() == rhs.as_slice()
    }

    fn ne(&self, rhs:&Blade<U,N2,G2>) -> bool {
        self.dim() != rhs.dim() || self.grade() != rhs.grade() || self.as_slice() != rhs.as_slice()
    }
}

impl<T, U, N1:Dim, N2:Dim> PartialEq<Rotor<U,N2>> for Rotor<T,N1>
where
    T: AllocRotor<N1> + PartialEq<U>,
    U: AllocRotor<N2>
{
    fn eq(&self, rhs:&Rotor<U,N2>) -> bool {
        self.dim() == rhs.dim() && self.as_slice() == rhs.as_slice()
    }

    fn ne(&self, rhs:&Rotor<U,N2>) -> bool {
        self.dim() != rhs.dim() || self.as_slice() != rhs.as_slice()
    }
}

impl<T, U, N1:Dim, N2:Dim> PartialEq<Multivector<U,N2>> for Multivector<T,N1>
where
    T: AllocMultivector<N1> + PartialEq<U>,
    U: AllocMultivector<N2>
{
    fn eq(&self, rhs:&Multivector<U,N2>) -> bool {
        self.dim() == rhs.dim() && self.as_slice() == rhs.as_slice()
    }

    fn ne(&self, rhs:&Multivector<U,N2>) -> bool {
        self.dim() != rhs.dim() || self.as_slice() != rhs.as_slice()
    }
}
