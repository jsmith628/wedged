#![cfg_attr(test, allow(soft_unstable))]
#![cfg_attr(test, feature(test))]

#[cfg(test)] extern crate test;

extern crate num_traits;
extern crate nalgebra as na;

pub mod basis_blade;
pub mod base;

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

//TODO maybe make binom and rotor_elements private

pub const fn rotor_elements(n:u32) -> usize {
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
/// # use galgebra::components_in;
///
/// assert_eq!(components_in(0).collect::<Vec<_>>(), vec![1]);
/// assert_eq!(components_in(1).collect::<Vec<_>>(), vec![1, 1]);
/// assert_eq!(components_in(2).collect::<Vec<_>>(), vec![1, 2, 1]);
/// assert_eq!(components_in(3).collect::<Vec<_>>(), vec![1, 3, 3, 1]);
/// assert_eq!(components_in(4).collect::<Vec<_>>(), vec![1, 4, 6, 4, 1]);
/// assert_eq!(components_in(5).collect::<Vec<_>>(), vec![1, 5, 10, 10, 5, 1]);
/// assert_eq!(components_in(6).collect::<Vec<_>>(), vec![1, 6, 15, 20, 15, 6, 1]);
///
/// ```
///
pub fn components_in(n: usize) -> impl std::iter::Iterator<Item=usize> {
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
/// # use galgebra::even_components_in;
///
/// assert_eq!(even_components_in(0).collect::<Vec<_>>(), vec![1]);
/// assert_eq!(even_components_in(1).collect::<Vec<_>>(), vec![1]);
/// assert_eq!(even_components_in(2).collect::<Vec<_>>(), vec![1, 1]);
/// assert_eq!(even_components_in(3).collect::<Vec<_>>(), vec![1, 3]);
/// assert_eq!(even_components_in(4).collect::<Vec<_>>(), vec![1, 6, 1]);
/// assert_eq!(even_components_in(5).collect::<Vec<_>>(), vec![1, 10, 5]);
/// assert_eq!(even_components_in(6).collect::<Vec<_>>(), vec![1, 15, 15, 1]);
///
/// ```
///
pub fn even_components_in(n: usize) -> impl std::iter::Iterator<Item=usize> {
    components_in(n).step_by(2)
}

pub trait DimName: na::dimension::DimName {}
impl<const N: usize> DimName for na::dimension::Const<N> {}

pub trait RefMul<Rhs:?Sized> {
    type Output;
    fn ref_mul<'a,'b>(&'a self, rhs:&'b Rhs) -> Self::Output;
}

impl<T1:?Sized,T2:?Sized,U> RefMul<T2> for T1 where for<'a,'b> &'a T1: std::ops::Mul<&'b T2,Output=U> {
    type Output = U;
    fn ref_mul<'a,'b>(&'a self, rhs:&'b T2) -> U { self * rhs }
}
