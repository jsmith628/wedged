
use std::borrow::{Borrow, BorrowMut};
use std::ops::{Index, IndexMut};
use nalgebra::base::dimension::{Dim, DimName};

pub unsafe trait Storage<T:Clone, N:Dim, G:Dim>:
    Clone + Index<usize, Output=T> + IndexMut<usize> + Borrow<[T]> + BorrowMut<[T]>
{
    fn dim(&self) -> N;
    fn grade(&self) -> G;
}

unsafe impl<T:Clone, N:DimName, G:DimName, const L: usize> Storage<T, N, G> for [T;L] {
    fn dim(&self) -> N { N::name() }
    fn grade(&self) -> G { G::name() }
}

unsafe impl<T:Clone, N:DimName, G:DimName> Storage<T, N, G> for Vec<T> {
    fn dim(&self) -> N { N::name() }
    fn grade(&self) -> G { G::name() }
}

#[derive(Clone)]
pub struct DynStorage<T,N:Dim,G:Dim> {
    data: Vec<T>,
    dim: N,
    grade: G
}

impl<T,N:Dim,G:Dim> Index<usize> for DynStorage<T,N,G> {
    type Output = T;
    fn index(&self, i: usize) -> &T { &self.data[i] }
}

impl<T,N:Dim,G:Dim> IndexMut<usize> for DynStorage<T,N,G> {
    fn index_mut(&mut self, i: usize) -> &mut T { &mut self.data[i] }
}

impl<T,N:Dim,G:Dim> Borrow<[T]> for DynStorage<T,N,G> {
    fn borrow(&self) -> &[T] { self.data.borrow() }
}

impl<T,N:Dim,G:Dim> BorrowMut<[T]> for DynStorage<T,N,G> {
    fn borrow_mut(&mut self) -> &mut [T] { self.data.borrow_mut() }
}

unsafe impl<T:Clone,N:Dim,G:Dim> Storage<T,N,G> for DynStorage<T,N,G> {
    fn dim(&self) -> N { self.dim }
    fn grade(&self) -> G { self.grade }
}
