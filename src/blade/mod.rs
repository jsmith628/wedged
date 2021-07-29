
use std::convert::{AsRef, AsMut};
use std::borrow::{Borrow, BorrowMut};
use std::hash::{Hash, Hasher};
use std::iter::{repeat, repeat_with};
use std::mem::MaybeUninit;
use std::ops::{
    Index, IndexMut,
    Add, AddAssign, Sub, SubAssign, Neg,
    Mul, Div, BitXor
};

use num_traits::Zero;

use na::dimension::{
    Dim, DimAdd, DimSum, DimNameDiff,
    Dynamic, U0, U1, U2, U3, U4, U5, U6
};

use crate::storage::{Storage, UninitStorage};
use crate::alloc::{Alloc, Allocate};
use crate::DimName;

pub type Iter<'a, T> = std::slice::Iter<'a, T>;
pub type IterMut<'a, T> = std::slice::IterMut<'a, T>;

pub struct Blade<T:Alloc<N,G>, N:Dim, G:Dim> {
    pub data: Allocate<T,N,G>
}

impl<T:Alloc<N,G>, N:Dim, G:Dim> Blade<T,N,G> {

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
    /// # use galgebra::blade::*;
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
    /// # use galgebra::blade::*;
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
    /// # use galgebra::blade::*;
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

impl<T:Alloc<N,G>, N:Dim, G:Dim> Clone for Blade<T,N,G> where Allocate<T,N,G>: Clone {
    fn clone(&self) -> Self { Blade { data: self.data.clone() } }
    fn clone_from(&mut self, src: &Self) { self.data.clone_from(&src.data) }
}

impl<T:Alloc<N,G>, N:Dim, G:Dim> Copy for Blade<T,N,G> where Allocate<T,N,G>: Copy {}

impl<T:Alloc<N,G>, N:Dim, G:Dim> AsRef<[T]> for Blade<T,N,G> {
    fn as_ref(&self) -> &[T] { self.data.as_ref() }
}

impl<T:Alloc<N,G>, N:Dim, G:Dim> AsMut<[T]> for Blade<T,N,G> {
    fn as_mut(&mut self) -> &mut [T] { self.data.as_mut() }
}

impl<T:Alloc<N,G>, N:Dim, G:Dim> Borrow<[T]> for Blade<T,N,G> {
    fn borrow(&self) -> &[T] { self.data.borrow() }
}

impl<T:Alloc<N,G>, N:Dim, G:Dim> BorrowMut<[T]> for Blade<T,N,G> {
    fn borrow_mut(&mut self) -> &mut [T] { self.data.borrow_mut() }
}


impl<T:Alloc<N,G>+Eq, N:Dim, G:Dim> Eq for Blade<T,N,G> {}

impl<T, U, N1:Dim, N2:Dim, G1:Dim, G2:Dim> PartialEq<Blade<U,N2,G2>> for Blade<T,N1,G1>
where
    T: Alloc<N1,G1> + PartialEq<U>,
    U: Alloc<N2,G2>
{
    fn eq(&self, rhs:&Blade<U,N2,G2>) -> bool {
        self.dim() == rhs.dim() && self.grade() == rhs.grade() && self.as_slice() == rhs.as_slice()
    }

    fn ne(&self, rhs:&Blade<U,N2,G2>) -> bool {
        self.dim() != rhs.dim() || self.grade() != rhs.grade() || self.as_slice() != rhs.as_slice()
    }
}

impl<T:Alloc<N,G>+Hash, N:Dim, G:Dim> Hash for Blade<T,N,G> {
    fn hash<H:Hasher>(&self, h: &mut H) {
        T::hash_slice(self.borrow(), h)
    }
}

impl<T:Alloc<N,G>, N:Dim, G:Dim> IntoIterator for Blade<T,N,G> {
    type Item = T;
    type IntoIter = <Allocate<T,N,G> as Storage<T,N,G>>::Iter;
    fn into_iter(self) -> Self::IntoIter {
        self.data.into_iter()
    }
}

impl<'a, T:Alloc<N,G>, N:Dim, G:Dim> IntoIterator for &'a Blade<T,N,G> {
    type Item = &'a T;
    type IntoIter = Iter<'a, T>;
    fn into_iter(self) -> Self::IntoIter { self.iter() }
}

impl<'a, T:Alloc<N,G>, N:Dim, G:Dim> IntoIterator for &'a mut Blade<T,N,G> {
    type Item = &'a mut T;
    type IntoIter = IterMut<'a, T>;
    fn into_iter(self) -> Self::IntoIter { self.iter_mut() }
}

impl<T,N:Dim,G1:Dim,G2:Dim> BitXor<Blade<T,N,G2>> for Blade<T,N,G1> where
    T: Mul<T,Output=T> + Alloc<N,G1> + Alloc<N,G2> + Alloc<N,DimSum<G1,G2>>,
    G1: DimAdd<G2>,
{
    type Output = Blade<T,N,DimSum<G1, G2>>;
    fn bitxor(self, rhs: Blade<T,N,G2>) -> Self::Output { unimplemented!() }
}
