
use super::*;

use std::ops::BitOr;
use typenum::{
    IsLessOrEqual, Sum, LeEq, True, U1
};

///
/// Marks if a [SimpleBlade] can be mutated entry-wise while staying simple
///
/// This trait is implemented on all simple scalars, vectors, psuedovectors, and psuedoscalars, and
/// is used as a bound to let those types be mutated arbitrarily via indexing, borrowing,
/// addition, etc.
///
/// At the moment, the implementation uses `typenum` expressions to determine type eligibility,
/// so there may be some provability issues with using generic types for the time being, especially
/// for psuedoscalars and psuedovectors. However, once the `#[marker]` feature is stabilized,
/// this will be simplified dramatically and there should be no more issues.
///
pub trait MutSimpleBlade {}

// this will be a #[marker] trait when that feature is stabilized

// impl<T:AllocBlade<N,U0>,N:Dim>     MutSimpleBlade for SimpleBlade<T,N,U0> {}
// impl<T:AllocBlade<N,U1>,N:Dim>     MutSimpleBlade for SimpleBlade<T,N,U1> {}
// impl<T:AllocBlade<N,N>, N:DimName> MutSimpleBlade for SimpleBlade<T,N,N>  {}
// impl<T:AllocBlade<N,DimDiff<N,U1>>, N:DimName+DimSub<U1>> MutSimpleBlade for SimpleBlade<T,N,DimDiff<N,U1>> {}

impl<T:AllocBlade<N,G>, N, G> MutSimpleBlade for SimpleBlade<T,N,G> where
    //establish that `N` and `G` are constant numbers
    N: DimName+ToTypenum,
    G: DimName+ToTypenum,

    //establish that we can compare `G` with `1` and `N` with `G+1`
    G::Typenum: Add<U1> + IsLessOrEqual<U1>,
    N::Typenum: IsLessOrEqual<Sum<G::Typenum,U1>>,

    //`or` together the two comparisons
    LeEq<G::Typenum, U1>: BitOr<LeEq<N::Typenum, Sum<G::Typenum,U1>>, Output=True>

{}

impl<T:AllocBlade<N,G>,N:Dim,G:Dim> DerefMut for SimpleBlade<T,N,G> where Self:MutSimpleBlade {
    fn deref_mut(&mut self) -> &mut Blade<T,N,G> { &mut self.data }
}

impl<T:AllocBlade<N,G>,N:Dim,G:Dim> IndexMut<usize> for SimpleBlade<T,N,G> where Self:MutSimpleBlade {
    fn index_mut(&mut self, i:usize) -> &mut T { &mut self.data[i] }
}

impl<T:AllocBlade<N,G>,N:Dim,G:Dim> AsMut<[T]> for SimpleBlade<T,N,G> where Self:MutSimpleBlade {
    fn as_mut(&mut self) -> &mut [T] { self.data.as_mut() }
}

impl<T:AllocBlade<N,G>,N:Dim,G:Dim> AsMut<Blade<T,N,G>> for SimpleBlade<T,N,G> where Self:MutSimpleBlade {
    fn as_mut(&mut self) -> &mut Blade<T,N,G> { &mut self.data }
}

impl<T:AllocBlade<N,G>,N:Dim,G:Dim> BorrowMut<[T]> for SimpleBlade<T,N,G> where Self:MutSimpleBlade {
    fn borrow_mut(&mut self) -> &mut [T] { self.data.borrow_mut() }
}

impl<T:AllocBlade<N,G>,N:Dim,G:Dim> BorrowMut<Blade<T,N,G>> for SimpleBlade<T,N,G> where Self:MutSimpleBlade {
    fn borrow_mut(&mut self) -> &mut Blade<T,N,G> { &mut self.data }
}

impl<'a,T:AllocBlade<N,G>,N:Dim,G:Dim> IntoIterator for &'a mut SimpleBlade<T,N,G> where Self:MutSimpleBlade {
    type Item = &'a mut T;
    type IntoIter = IterMut<'a,T>;
    fn into_iter(self) -> IterMut<'a,T> { (&mut self.data).into_iter() }
}

impl<'a,T:AllocBlade<N,G>,N:Dim,G:Dim> SimpleBlade<T,N,G> where Self:MutSimpleBlade {
    pub fn as_inner_mut(&mut self) -> &mut Blade<T,N,G> { &mut self.data }
}
