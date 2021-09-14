#![cfg_attr(test, allow(soft_unstable))]
#![cfg_attr(test, feature(test))]

#[cfg(test)] extern crate test;

#[macro_use]
extern crate derivative;
extern crate approx;
extern crate num_traits;
extern crate nalgebra as na;

//TODO: add impls for Wrapping<T> and Saturating<T>
macro_rules! impl_forward_scalar_binops {
    (
        $prim:ident; impl<T:$Alloc:ident,$($N:ident),*> $Op:ident.$op:ident() for $Ty:ident;
        $($a:lifetime)?; $($b:lifetime)?
    ) => {
        impl<$($a,)? $($b,)? $($N:Dim),*> $Op<$(&$b)? $Ty<$prim,$($N),*>> for $(&$a)? $prim where $prim:$Alloc<$($N),*> {
            type Output = $Ty<$prim,$($N),*>;
            fn $op(self, rhs: $(&$b)? $Ty<$prim,$($N),*>) -> $Ty<$prim,$($N),*> {
                rhs.$op(self)
            }
        }
    };

    (; $($rest:tt)*) => {};

    ($p:ident $($prim:ident)*; $($tt:tt)*) => {
        impl_forward_scalar_binops!($p; $($tt)*;   ;   );
        impl_forward_scalar_binops!($p; $($tt)*;   ; 'b);
        impl_forward_scalar_binops!($p; $($tt)*; 'a;   );
        impl_forward_scalar_binops!($p; $($tt)*; 'a; 'b);
        impl_forward_scalar_binops!($($prim)*; $($tt)*);
    };

    ($($tt:tt)*) => {
        impl_forward_scalar_binops!(u8 i8 u16 i16 u32 i32 u64 i64 u128 i128 usize isize f32 f64; $($tt)*);
    };
}

macro_rules! impl_eq {

    () => {};

    (
        $Ty1:ident<T:$Alloc1:ident $(, $N1:ident)*> == $Ty2:ident<T:$Alloc2:ident $(, $N2:ident)*>
        with |$self:ident, $rhs:ident| $cond:expr, $field1:expr, $field2:expr;
        $($rest:tt)*
    ) => {

        impl<T1, T2 $(, $N1:Dim)* $(, $N2:Dim)*> PartialEq<$Ty2<T2 $(,$N2)*>> for $Ty1<T1 $(,$N1)*>
        where
            T1: $Alloc1<$($N1),*> + PartialEq<T2>,
            T2: $Alloc2<$($N2),*>
        {
            fn eq(&$self, $rhs: &$Ty2<T2 $(,$N2)*>) -> bool { $cond && $field1.eq($field2) }
            fn ne(&$self, $rhs: &$Ty2<T2 $(,$N2)*>) -> bool { !$cond || $field1.ne($field2) }
        }

        impl<T1, T2 $(, $N1:Dim)* $(, $N2:Dim)*> AbsDiffEq<$Ty2<T2 $(,$N2)*>> for $Ty1<T1 $(,$N1)*>
        where
            T1: $Alloc1<$($N1),*> + AbsDiffEq<T2>,
            T2: $Alloc2<$($N2),*>,
            T1::Epsilon: Clone
        {

            type Epsilon = T1::Epsilon;

            fn default_epsilon() -> T1::Epsilon { T1::default_epsilon() }

            fn abs_diff_eq(&$self, $rhs: &$Ty2<T2 $(,$N2)*>, epsilon: T1::Epsilon) -> bool {
                $cond && $field1.abs_diff_eq($field2, epsilon)
            }

            fn abs_diff_ne(&$self, $rhs: &$Ty2<T2 $(,$N2)*>, epsilon: T1::Epsilon) -> bool {
                !$cond || $field1.abs_diff_ne($field2, epsilon)
            }
        }

        impl<T1, T2 $(, $N1:Dim)* $(, $N2:Dim)*> RelativeEq<$Ty2<T2 $(,$N2)*>> for $Ty1<T1 $(,$N1)*>
        where
            T1: $Alloc1<$($N1),*> + RelativeEq<T2>,
            T2: $Alloc2<$($N2),*>,
            T1::Epsilon: Clone
        {

            fn default_max_relative() -> T1::Epsilon { T1::default_max_relative() }

            fn relative_eq(&$self, $rhs: &$Ty2<T2 $(,$N2)*>, epsilon: T1::Epsilon, max_relative: T1::Epsilon) -> bool {
                $cond && $field1.relative_eq($field2, epsilon, max_relative)
            }

            fn relative_ne(&$self, $rhs: &$Ty2<T2 $(,$N2)*>, epsilon: T1::Epsilon, max_relative: T1::Epsilon) -> bool {
                !$cond || $field1.relative_ne($field2, epsilon, max_relative)
            }
        }

        impl<T1, T2 $(, $N1:Dim)* $(, $N2:Dim)*> UlpsEq<$Ty2<T2 $(,$N2)*>> for $Ty1<T1 $(,$N1)*>
        where
            T1: $Alloc1<$($N1),*> + UlpsEq<T2>,
            T2: $Alloc2<$($N2),*>,
            T1::Epsilon: Clone
        {

            fn default_max_ulps() -> u32 { T1::default_max_ulps() }

            fn ulps_eq(&$self, $rhs: &$Ty2<T2 $(,$N2)*>, epsilon: T1::Epsilon, max_ulps: u32) -> bool {
                $cond && $field1.ulps_eq($field2, epsilon, max_ulps)
            }

            fn ulps_ne(&$self, $rhs: &$Ty2<T2 $(,$N2)*>, epsilon: T1::Epsilon, max_ulps: u32) -> bool {
                !$cond || $field1.ulps_ne($field2, epsilon, max_ulps)
            }
        }

        impl_eq!($($rest)*);
    }

}

#[cfg(test)]
macro_rules! dim_name_test_loop {
    (@run ; $callback:ident) => {};
    (@run $N0:ident $($N:ident)*; $callback:ident) => {
        $callback!($N0);
        dim_name_test_loop!(@run $($N)*; $callback);
    };

    //$d must be the $ token
    (|$d:tt $N:ident| $($expr:tt)*) => {
        {

            #[allow(unused_imports)]
            use na::dimension::{
                DimName,
                U0, U1, U2, U3, U4, U5, U6, U7, U8, U9, U10
            };

            macro_rules! _dim_name_test_loop_callback {
                ($d $N:ident) => {
                    $($expr)*
                };
            }

            //if we do any more than U14, then we get stack overflows from the values being too large
            //for 64bit scalars
            //Also, compilation times get pretty long for this stuff, so we lower it down to U10
            //instead
            dim_name_test_loop!(
                @run U0 U1 U2 U3 U4 U5 U6 U7 U8 U9 U10;
                _dim_name_test_loop_callback
            );

        }
    };

    (|$d0:tt $N0:ident $(, $d:tt $N:ident)+| $($expr:tt)*) => {
        dim_name_test_loop!(
            |$d0 $N0| dim_name_test_loop!(|$($d $N),+| $($expr)*);
        );
    }


}


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
    if n==0 { 0 } else { 2usize.pow(n.saturating_sub(1)) }
}

pub const fn multivector_elements(n:u32) -> usize {
    2usize.pow(n)
}

pub const fn grade_index_in_versor(n:usize, g:usize) -> usize {
    if g<=1 { return 0; }
    binom(n, g-2) + grade_index_in_versor(n, g-2)
}

pub const fn grade_index_in_multivector(n:usize, g:usize) -> usize {
    if g==0 { return 0; }
    binom(n, g-1) + grade_index_in_multivector(n, g-1)
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

pub trait AddGroup: na::ClosedAdd + na::ClosedSub + std::ops::Neg<Output=Self> + num_traits::Zero {}
impl<T:na::ClosedAdd + na::ClosedSub + std::ops::Neg<Output=Self> + num_traits::Zero> AddGroup for T {}

pub trait Scale<Rhs=Self> {
    type Output;
    fn scale(self, rhs:Rhs) -> Self::Output;
}

pub trait InvScale<Rhs=Self> {
    type Output;
    fn inv_scale(self, rhs:Rhs) -> Self::Output;
}
