
use super::*;

//
// Impls that mutate the blade that only work if the blade is guaranteed to be simple
//

impl<T:AllocSimpleBlade<N,G>,N:Dim,G:Dim> DerefMut for SimpleBlade<T,N,G> {
    fn deref_mut(&mut self) -> &mut Blade<T,N,G> { &mut self.data }
}

impl<T:AllocSimpleBlade<N,G>,N:Dim,G:Dim> IndexMut<usize> for SimpleBlade<T,N,G> {
    fn index_mut(&mut self, i:usize) -> &mut T { &mut self.data[i] }
}

impl<T:AllocSimpleBlade<N,G>,N:Dim,G:Dim> AsMut<[T]> for SimpleBlade<T,N,G> {
    fn as_mut(&mut self) -> &mut [T] { self.data.as_mut() }
}

impl<T:AllocSimpleBlade<N,G>,N:Dim,G:Dim> AsMut<Blade<T,N,G>> for SimpleBlade<T,N,G> {
    fn as_mut(&mut self) -> &mut Blade<T,N,G> { &mut self.data }
}

impl<T:AllocSimpleBlade<N,G>,N:Dim,G:Dim> BorrowMut<[T]> for SimpleBlade<T,N,G> {
    fn borrow_mut(&mut self) -> &mut [T] { self.data.borrow_mut() }
}

impl<T:AllocSimpleBlade<N,G>,N:Dim,G:Dim> BorrowMut<Blade<T,N,G>> for SimpleBlade<T,N,G> {
    fn borrow_mut(&mut self) -> &mut Blade<T,N,G> { &mut self.data }
}

impl<'a,T:AllocSimpleBlade<N,G>,N:Dim,G:Dim> IntoIterator for &'a mut SimpleBlade<T,N,G> {
    type Item = &'a mut T;
    type IntoIter = IterMut<'a,T>;
    fn into_iter(self) -> IterMut<'a,T> { (&mut self.data).into_iter() }
}

impl<T:AllocSimpleBlade<N,G>,N:DimName,G:DimName> FromIterator<T> for SimpleBlade<T,N,G> {
    fn from_iter<I:IntoIterator<Item=T>>(i:I) -> SimpleBlade<T,N,G> { Self::from(Blade::from_iter(i)) }
}

impl<T:AllocSimpleBlade<N,G>+Default,N:DimName,G:DimName> Default for SimpleBlade<T,N,G> {
    fn default() -> SimpleBlade<T,N,G> { Self::from(Blade::default()) }
}

impl<T:AllocSimpleBlade<N,G>,N:Dim,G:Dim> From<Blade<T,N,G>> for SimpleBlade<T,N,G> {
    fn from(x: Blade<T,N,G>) -> SimpleBlade<T,N,G> { Self { data: x } }
}

impl<T:AllocSimpleBlade<N,G>,N:Dim,G:Dim> SimpleBlade<T,N,G> {
    /// Unwraps `self` and a mutable reference of its inner [algebraic](galgebra::algebra) struct
    pub fn as_inner_mut(&mut self) -> &mut Blade<T,N,G> { &mut self.data }

    /// Creates a new value of `Self` from its inner algebraic struct
    ///
    /// Since `T:AllocSimpleBlade<N,G>`, this is guarranteed to satisfy all the preconditions of this type 
    pub fn from_inner(inner: Blade<T,N,G>) -> Self { Self { data: inner } }
}
