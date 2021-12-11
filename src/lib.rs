#![cfg_attr(test, allow(soft_unstable))]
#![cfg_attr(test, feature(test))]
#![cfg_attr(feature = "fn_traits", feature(fn_traits, unboxed_closures))]


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
