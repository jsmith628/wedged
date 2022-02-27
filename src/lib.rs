#![doc = include_str!("../README.md")]
#![recursion_limit = "1024"]
#![cfg_attr(test, allow(soft_unstable))]
#![cfg_attr(test, feature(test))]
#![cfg_attr(feature = "fn_traits", feature(fn_traits, unboxed_closures))]

#![feature(trace_macros)]


#[cfg(test)] extern crate test;

#[macro_use]
extern crate derivative;
#[cfg(feature = "code-gen")] extern crate wedged_macros;

extern crate basis_blade;
extern crate approx;
extern crate num_traits;
extern crate nalgebra as na;

//16D should work ok... a 16D multivector takes *only* 65K components, but if this takes
//too much memory, we may need to lower it a little :/
#[cfg(test)] pub(crate) const TEST_DIM: usize = 16;
#[cfg(test)] pub(crate) const SHORT_TEST_DIM: usize = 6;

macro_rules! borrow {
    ($e:expr, $a:lifetime) => { $e };
    ($e:expr, ) => { &$e };
}

macro_rules! cast_dim_doc {
    () => {
        "Embeds `self` into a different dimension by either removing elements or inserting zeros"
    }
}

macro_rules! new_docs {
    //starts the loop
    ($ty:ident::new($($arg:ident),*);) => { new_docs!(@vals 0 $($arg)*; $ty) };

    //picks out the numbers that will be used in the doc test
    (@vals 0  $arg:ident $($tt:tt)*) => { new_docs!(@vals 1  $($tt)* $arg 6) };
    (@vals 1  $arg:ident $($tt:tt)*) => { new_docs!(@vals 2  $($tt)* $arg 2) };
    (@vals 2  $arg:ident $($tt:tt)*) => { new_docs!(@vals 3  $($tt)* $arg 8) };
    (@vals 3  $arg:ident $($tt:tt)*) => { new_docs!(@vals 4  $($tt)* $arg 3) };
    (@vals 4  $arg:ident $($tt:tt)*) => { new_docs!(@vals 5  $($tt)* $arg 1) };
    (@vals 5  $arg:ident $($tt:tt)*) => { new_docs!(@vals 6  $($tt)* $arg 8) };
    (@vals 6  $arg:ident $($tt:tt)*) => { new_docs!(@vals 7  $($tt)* $arg 5) };
    (@vals 7  $arg:ident $($tt:tt)*) => { new_docs!(@vals 8  $($tt)* $arg 3) };
    (@vals 8  $arg:ident $($tt:tt)*) => { new_docs!(@vals 9  $($tt)* $arg 0) };
    (@vals 9  $arg:ident $($tt:tt)*) => { new_docs!(@vals 10 $($tt)* $arg 7) };
    (@vals 10 $arg:ident $($tt:tt)*) => { new_docs!(@vals 11 $($tt)* $arg 1) };
    (@vals 11 $arg:ident $($tt:tt)*) => { new_docs!(@vals 12 $($tt)* $arg 7) };
    (@vals 12 $arg:ident $($tt:tt)*) => { new_docs!(@vals 13 $($tt)* $arg 9) };
    (@vals 13 $arg:ident $($tt:tt)*) => { new_docs!(@vals 14 $($tt)* $arg 5) };
    (@vals 14 $arg:ident $($tt:tt)*) => { new_docs!(@vals 15 $($tt)* $arg 8) };
    (@vals 15 $arg:ident $($tt:tt)*) => { new_docs!(@vals 16 $($tt)* $arg 6) };
    (@vals 16 $arg:ident $($tt:tt)*) => { new_docs!(@vals 17 $($tt)* $arg 4) };
    (@vals 17 $arg:ident $($tt:tt)*) => { new_docs!(@vals 18 $($tt)* $arg 7) };
    (@vals 18 $arg:ident $($tt:tt)*) => { new_docs!(@vals 19 $($tt)* $arg 6) };
    (@vals 19 $arg:ident $($tt:tt)*) => { new_docs!(@vals 20 $($tt)* $arg 9) };

    //creates the function at the end of the vals loop
    (@vals $n:literal; $ty:ident $($arg:ident $val:literal)*) => {
        concat!(
            //yes, this is kinda gross, but it *does* work
            "Constructs a [`", stringify!($ty), "`] directly from components\n",
            "\n",
            " # Examples\n",
            "```\n",
            " # #[allow(unused_imports)] use wedged::algebra::*;\n",
            " # #[allow(unused_imports)] use wedged::subspace::*;\n",
            "let arr = [", stringify!($($val),*), "];\n",
            "let x = ", stringify!($ty), "::new(", stringify!($($val),*), ");\n",
            "\n",
            "assert_eq!(x.as_slice(), &arr);\n",
            "```"
        )
    }
}

//Takes in normal rust code and quotes it but with a basic impl of trait aliases added
macro_rules! auto {

    //doing this means that we can ignore the trailing semicolon
    (
        @lines {
            $(#[$attr:meta])*
            $vis:vis trait $trait:ident$(<$($T:ident),*>)? = $($bound:tt)*
        } ;
        $($rest:tt)*
    ) => {

        $(#[$attr])*
        $vis trait $trait$(<$($T),*>)?: $($bound)* {}

        impl<X $(, $($T),*)?> $trait$(<$($T),*>)? for X where X: $($bound)* {}

        auto!($($rest)*);
    };

    //munches through the code until we have a full line or block
    (@lines {$($line:tt)*} ) => { $($line)* };
    (@lines {$($line:tt)*} ; $($rest:tt)*) => { $($line)*; auto!(@lines {} $($rest)*); };
    (@lines {$($line:tt)*} {} $($rest:tt)*) => { $($line)*{} auto!(@lines {} $($rest)*); };
    (@lines {$($line:tt)*} $tt:tt $($rest:tt)*) => { auto!(@lines {$($line)* $tt} $($rest)*); };

    //ends the macro if we have nothing left
    () => {};

    //starts the loop to split off each line (we gotta be careful tho since this can lead to really
    //nasty errors)
    ($($stuff:tt)*) => { auto!(@lines {} $($stuff)*); };

}

macro_rules! impl_forward_scalar_binops {
    (
        @impl
        $prim:ty; impl<T:$Alloc:ident,$($N:ident),*> $Op:ident.$op:ident() for $Ty:ident;
        $($a:lifetime)?; $($b:lifetime)?
    ) => {
        impl<$($a,)? $($b,)? $($N:Dim),*> $Op<$(&$b)? $Ty<$prim,$($N),*>> for $(&$a)? $prim where $prim:$Alloc<$($N),*> {
            type Output = $Ty<$prim,$($N),*>;
            fn $op(self, rhs: $(&$b)? $Ty<$prim,$($N),*>) -> $Ty<$prim,$($N),*> {
                rhs.$op(self)
            }
        }
    };

    (@loop ; $($rest:tt)*) => {};

    (@loop $p:ty, $($prim:ty,)*; $($tt:tt)*) => {

        impl_forward_scalar_binops!(@impl $p; $($tt)*;   ;   );
        impl_forward_scalar_binops!(@impl $p; $($tt)*;   ; 'b);
        impl_forward_scalar_binops!(@impl $p; $($tt)*; 'a;   );
        impl_forward_scalar_binops!(@impl $p; $($tt)*; 'a; 'b);

        impl_forward_scalar_binops!(@loop $($prim,)*; $($tt)*);
    };

    ($($tt:tt)*) => {
        impl_forward_scalar_binops!(
            @loop
            u8, i8, u16, i16, u32, i32, u64, i64, u128, i128, usize, isize, f32, f64,
            // ::std::num::Wrapping<u8>,    ::std::num::Wrapping<i8>,
            // ::std::num::Wrapping<u16>,   ::std::num::Wrapping<i16>,
            // ::std::num::Wrapping<u32>,   ::std::num::Wrapping<i32>,
            // ::std::num::Wrapping<u64>,   ::std::num::Wrapping<i64>,
            // ::std::num::Wrapping<u128>,  ::std::num::Wrapping<i128>,
            // ::std::num::Wrapping<usize>, ::std::num::Wrapping<isize>,
            ;$($tt)*
        );
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

//implements Sum and/or Product using fold()
macro_rules! impl_fold {
    (
        impl<T:$Alloc2:ident,U:$Alloc1:ident,$($N:ident),*>
        $Op:ident<$Ty2:ident<T,$($N2:ident),*>>.$op:ident() for $Ty1:ident<U,$($N1:ident),*>
        with $Op2:ident.$op2:ident(), $Id:ident.$id:ident()
        ; $($a:lifetime)? $(where $($tt:tt)*)?
    ) => {

        //
        // There were a couple options for how to do this.
        // One was to use Add and Mul with fold, and the other would be to split the
        // iterator by index, use Sum, and recombine. Theoretically, there could be benefits to
        // the latter in efficiency with more complex types and in correctness. But the added
        // implementation and API complexity didn't quite seem worth it for probably only a very
        // minor gain
        //

        impl<$($a,)? T,U,$($N:Dim),*> $Op<$(&$a)? $Ty2<T,$($N2),*>> for $Ty1<U,$($N1),*>
        where
            T: $Alloc2<$($N2),*>,
            U: $Alloc1<$($N1),*>,
            $Ty1<U,$($N1),*>: $Op2<$(&$a)? $Ty2<T,$($N2),*>, Output=$Ty1<U,$($N1),*>> + $Id
            $(, $($tt)*)?
        {
            fn $op<I>(i:I) -> $Ty1<U,$($N1),*> where I: Iterator<Item=$(&$a)? $Ty2<T,$($N2),*>> {
                i.fold($Id::$id(), |c,x| c.$op2(x))
            }
        }

    };

    (
        impl<T:$Alloc1:ident,U:$Alloc2:ident,$($N:ident),*>
        Sum<$Ty2:ident<T,$($N2:ident),*>> for $Ty1:ident<U,$($N1:ident),*>
        $(where $($tt:tt)*)?
    ) => {
        impl_fold!(
            impl<T:$Alloc1,U:$Alloc2,$($N),*> Sum<$Ty2<T,$($N2),*>>.sum() for $Ty1<U,$($N1),*>
            with Add.add(), Zero.zero() ; $(where $($tt)*)?
        );
        impl_fold!(
            impl<T:$Alloc1,U:$Alloc2,$($N),*> Sum<$Ty2<T,$($N2),*>>.sum() for $Ty1<U,$($N1),*>
            with Add.add(), Zero.zero() ; 'a $(where $($tt)*)?
        );
    };

    (
        impl<T:$Alloc1:ident,U:$Alloc2:ident,$($N:ident),*>
        Product<$Ty2:ident<T,$($N2:ident),*>> for $Ty1:ident<U,$($N1:ident),*>
        $(where $($tt:tt)*)?
    ) => {
        impl_fold!(
            impl<T:$Alloc1,U:$Alloc2,$($N),*> Product<$Ty2<T,$($N2),*>>.product() for $Ty1<U,$($N1),*>
            with Mul.mul(), One.one() ; $(where $($tt)*)?
        );
        impl_fold!(
            impl<T:$Alloc1,U:$Alloc2,$($N),*> Product<$Ty2<T,$($N2),*>>.product() for $Ty1<U,$($N1),*>
            with Mul.mul(), One.one() ; 'a $(where $($tt)*)?
        );
    };

}

#[cfg(test)]
macro_rules! dim_name_test_loop {
    (@run ; $callback:ident) => {};
    (@run $N0:ident $($N:ident)*; $callback:ident) => {
        $callback!($N0);
        dim_name_test_loop!(@run $($N)*; $callback);
    };

    (|$d:tt $N:ident| $($expr:tt)*) => {
        dim_name_test_loop!({U0 U1 U2 U3 U4 U5 U6 U7 U8 U9 U10} |$d $N| $($expr)*);
    };

    (@short |$d:tt $N:ident| $($expr:tt)*) => {
        dim_name_test_loop!({U0 U1 U2 U3 U4 U5 U6} |$d $N| $($expr)*);
    };

    //$d must be the $ token
    ({$($U:ident)*} |$d:tt $N:ident| $($expr:tt)*) => {
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
                @run $($U)*;
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

pub mod algebra;
pub mod subspace;
