
use std::ops::*;

extern crate num_traits;

use nalgebra::base::dimension::*;

use self::alloc::*;

pub mod storage;
pub mod alloc;
pub mod basis_blade;

///
/// Computes the [binomial coefficient](1) of n terms at position k.
///
/// Said differently, finds the number of combinations of k objects from a set of n things.
/// This is icredibly important for geometric algebra since this is how we compute the number of
/// bases for an n-dimensional blade of grade g.
///
/// [1]: https://en.wikipedia.org/wiki/Binomial_coefficient
///
/// # Examples
///
///```
/// # use galgebra::binom;
///
/// //The first three rows of Pascal's triangle
///
/// assert_eq!(binom(0,0), 1);
///
/// assert_eq!(binom(1,0), 1);
/// assert_eq!(binom(1,1), 1);
///
/// assert_eq!(binom(2,0), 1);
/// assert_eq!(binom(2,1), 2);
/// assert_eq!(binom(2,2), 1);
///
/// assert_eq!(binom(3,0), 1);
/// assert_eq!(binom(3,1), 3);
/// assert_eq!(binom(3,2), 3);
/// assert_eq!(binom(3,3), 1);
///
/// //we get 0 if and only if k>n:
/// for n in 0..10 {
///     for k in 0..10 {
///         assert_eq!(k>n, binom(n,k)==0);
///     }
/// }
///
///
///```
///
pub const fn binom(n:usize, k:usize) -> usize {

    //base cases
    if k>n { return 0; }
    if k==0 { return 1; }

    //Note that we are guaranteed that this division has no remainder specifically because we
    //compute the numerator and denominator in this order
    (n-k+1) * binom(n, k-1) / k
}

#[derive(Clone)]
pub struct Blade<T:Alloc<N,G>, N: Dim, G: Dim> {
    pub data: Allocate<T,N,G>
}

impl<T:Alloc<N,G>, N: Dim, G: Dim> Copy for Blade<T,N,G> where Allocate<T,N,G>: Copy {}


impl<T,N:Dim,G1:Dim,G2:Dim> BitXor<Blade<T,N,G2>> for Blade<T,N,G1> where
    T: Mul<T,Output=T> + Alloc<N,G1> + Alloc<N,G2> + Alloc<N,DimSum<G1,G2>>,
    G1: DimAdd<G2>,
{
    type Output = Blade<T,N,DimSum<G1, G2>>;
    fn bitxor(self, rhs: Blade<T,N,G2>) -> Self::Output { unimplemented!() }
}
