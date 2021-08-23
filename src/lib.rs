#![cfg_attr(test, allow(soft_unstable))]
#![cfg_attr(test, feature(test))]

#[cfg(test)] extern crate test;

#[macro_use]
extern crate derivative;
extern crate num_traits;
extern crate nalgebra as na;

pub mod base;

pub mod basis_blade;
pub mod algebra;
pub mod subspace;

///
/// Computes the [binomial coefficient][1] of n terms at position k.
///
/// Said differently, finds the number of combinations of k objects from a set of n things.
/// This is incredibly important for geometric algebra since this is how we compute the number of
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

//TODO maybe make these private

pub const fn even_elements(n:u32) -> usize {
    2usize.pow(n.saturating_sub(1))
}

pub const fn odd_elements(n:u32) -> usize {
    2usize.pow(n.saturating_sub(1))
}

pub const fn multivector_elements(n:u32) -> usize {
    2usize.pow(n)
}

///
/// Iterates over the number of elements of each blade in the given dimension
///
/// # Examples
/// ```
/// # use galgebra::components_of;
///
/// assert_eq!(components_of(0).collect::<Vec<_>>(), vec![1]);
/// assert_eq!(components_of(1).collect::<Vec<_>>(), vec![1, 1]);
/// assert_eq!(components_of(2).collect::<Vec<_>>(), vec![1, 2, 1]);
/// assert_eq!(components_of(3).collect::<Vec<_>>(), vec![1, 3, 3, 1]);
/// assert_eq!(components_of(4).collect::<Vec<_>>(), vec![1, 4, 6, 4, 1]);
/// assert_eq!(components_of(5).collect::<Vec<_>>(), vec![1, 5, 10, 10, 5, 1]);
/// assert_eq!(components_of(6).collect::<Vec<_>>(), vec![1, 6, 15, 20, 15, 6, 1]);
///
/// ```
///
pub fn components_of(n: usize) -> impl std::iter::Iterator<Item=usize> {
    let mut binom = 1;
    (0..=n).map(
        move |g| {
            let result = binom;
            binom *= n-g;
            binom /= g+1;
            result
        }
    )
}

///
/// Iterates over the number of elements of each _even_ blade in the given dimension
///
/// # Examples
/// ```
/// # use galgebra::even_components_of;
///
/// assert_eq!(even_components_of(0).collect::<Vec<_>>(), vec![1]);
/// assert_eq!(even_components_of(1).collect::<Vec<_>>(), vec![1]);
/// assert_eq!(even_components_of(2).collect::<Vec<_>>(), vec![1, 1]);
/// assert_eq!(even_components_of(3).collect::<Vec<_>>(), vec![1, 3]);
/// assert_eq!(even_components_of(4).collect::<Vec<_>>(), vec![1, 6, 1]);
/// assert_eq!(even_components_of(5).collect::<Vec<_>>(), vec![1, 10, 5]);
/// assert_eq!(even_components_of(6).collect::<Vec<_>>(), vec![1, 15, 15, 1]);
///
/// ```
///
pub fn even_components_of(n: usize) -> impl std::iter::Iterator<Item=usize> {
    components_of(n).step_by(2)
}

///
/// Iterates over the number of elements of each _odd_ blade in the given dimension
///
/// # Examples
/// ```
/// # use galgebra::odd_components_of;
///
/// assert_eq!(odd_components_of(0).collect::<Vec<_>>(), vec![]);
/// assert_eq!(odd_components_of(1).collect::<Vec<_>>(), vec![1]);
/// assert_eq!(odd_components_of(2).collect::<Vec<_>>(), vec![2]);
/// assert_eq!(odd_components_of(3).collect::<Vec<_>>(), vec![3, 1]);
/// assert_eq!(odd_components_of(4).collect::<Vec<_>>(), vec![4, 4]);
/// assert_eq!(odd_components_of(5).collect::<Vec<_>>(), vec![5, 10, 1]);
/// assert_eq!(odd_components_of(6).collect::<Vec<_>>(), vec![6, 20, 6]);
///
/// ```
///
pub fn odd_components_of(n: usize) -> impl std::iter::Iterator<Item=usize> {
    components_of(n).skip(1).step_by(2)
}

pub trait RefMul<Rhs:?Sized> {
    type Output;
    fn ref_mul<'a,'b>(&'a self, rhs:&'b Rhs) -> Self::Output;
}

impl<T1:?Sized,T2:?Sized,U> RefMul<T2> for T1 where for<'a,'b> &'a T1: std::ops::Mul<&'b T2,Output=U> {
    type Output = U;
    fn ref_mul<'a,'b>(&'a self, rhs:&'b T2) -> U { self * rhs }
}

pub trait Scale<Rhs=Self> {
    type Output;
    fn scale(self, rhs:Rhs) -> Self::Output;
}

pub trait InvScale<Rhs=Self> {
    type Output;
    fn inv_scale(self, rhs:Rhs) -> Self::Output;
}
