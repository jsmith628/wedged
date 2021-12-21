//!
//! Traits for selecting types to store the internal data of the algebraic structs
//!
//! Ideally, this would be done using entirely `const` generics, but this is impossible for a
//! couple reasons:
//! 1. Unlike for simple vectors and matrices, the number of elements in blades, evens, etc
//!    is not simply the dimension or grade but instead a more involved function of them. Hence,
//!    since `const` expressions using generics aren't currently allowed in array sizes, we
//!    cannot use them to construct the backing array.
//! 2. We need to *also* support non-array storage for [`Dynamic`] dimensions and grades
//!
//! Instead, we use a trait based system with associated types to select what the backing buffer
//! should be.
//!
//! The core of this system are the [`AllocBlade<N,G>`], [`AllocEven<N>`], [`AllocOdd<N>`], and
//! [`AllocMultivector<N>`]. These are all given blanket `impl`s on all types with the generics `N`
//! and `G` filled in with every supported combination of dimension and grade.
//! Then, order retrieve the type used for storage in a particular algebraic struct, we can
//! use the corresponding `Alloc*` trait and use the `Buffer` associated type. And whenever
//! using a generic dimension or grade on an algebraic struct, we can just add an `Alloc*` bound
//! to the scalar in order to test support for that particular dimension/grade combination
//!
//! At the moment, only dimensions and grades up to 16 are supported for static array-based
//! allocation. This is due both to limitations of this system *and* out of practical considerations
//! regarding the amount of memory used by the structures in high numbers of dimensions.
//! (`f32` Multivectors in 16D already use ~**260KB**!!) However,
//! if a high number of dimensions are required, using a [`Dynamic`] dimension or grade will allow
//! that number of dimensions to be used, just using the heap instead
//!
//!

use std::mem::MaybeUninit;
use std::iter::Iterator;

use crate::base::*;

use std::ops::{ Add, BitOr };
use typenum::{
    IsLessOrEqual, Sum, LeEq, True, U1
};

#[cfg(doc)] use crate::algebra::*;
#[cfg(doc)] use crate::subspace::*;

/// Implements [`Alloc`] and makes the default choise for what storage types to use
pub struct DefaultAllocator;

/// The storage type to use for `M`
pub type Allocate<M> = <DefaultAllocator as Alloc<M>>::Buffer;

/// The backing buffer type for a [`Blade`] with scalar `T`, dimension `N`, and grade `G`
pub type AllocateBlade<T,N,G> = <T as AllocBlade<N,G>>::Buffer;

/// The backing buffer type for an [`Even`] with scalar `T` and dimension `N`
pub type AllocateEven<T,N> = <T as AllocEven<N>>::Buffer;

/// The backing buffer type for an [`Odd`] with scalar `T` and dimension `N`
pub type AllocateOdd<T,N> = <T as AllocOdd<N>>::Buffer;

/// The backing buffer type for a [`Multivector`] with scalar `T` and dimension `N`
pub type AllocateMultivector<T,N> = <T as AllocMultivector<N>>::Buffer;

///
/// Picks the buffer type to use for the generic type `M` and provides extra helper methods
///
/// This trait serves two purposes:
/// 1. Unifies the different algebraic systems into one trait to make some of the code more consistent
/// 2. Can be implemented on multiple structs to represent different systems of allocating backing
///   buffers. At the moment, the only one of these is [`DefaultAllocator`], but more might be added
///   in the future
///
pub unsafe trait Alloc<M> {

    ///The type to store in the backing buffer
    type Scalar: Sized;

    ///A type representing the dimension and/or grade of this structure
    type Shape: Copy;

    ///The type to store the data in
    type Buffer: Storage<Self::Scalar, Uninit=Self::Uninit>;

    ///The type to store uninitialized data in
    type Uninit: UninitStorage<Self::Scalar, Init=Self::Buffer>;

    ///Returns the dimension and potentially grade depending on what type `M` is
    fn shape(this: &M) -> Self::Shape;
    ///Makes an uninitialized buffer
    fn uninit(shape: Self::Shape) -> Self::Uninit;
    ///Creates an `M` from an uninitialized buffer assuming it is initialized
    unsafe fn assume_init(uninit: Self::Uninit) -> M;

}

///Picks the buffer to use for a [`Blade`] of dimension `N`, grade `G`, and using `Self` as the scalar
pub trait AllocBlade<N:Dim,G:Dim>: Sized {
    type Buffer: BladeStorage<Self,N,G>;
}

///Picks the buffer to use for an [`Even`] of dimension `N`, grade `G`, and using `Self` as the scalar
pub trait AllocEven<N:Dim>: Sized {
    type Buffer: EvenStorage<Self,N>;
}

///Picks the buffer to use for an [`Odd`] of dimension `N`, grade `G`, and using `Self` as the scalar
pub trait AllocOdd<N:Dim>: Sized {
    type Buffer: OddStorage<Self,N>;
}

///A marker trait for when a dimension `N` is supported for both [`Even`]s and [`Odd`]s
pub trait AllocVersor<N:Dim>: AllocEven<N> + AllocOdd<N> {}
impl<T:AllocEven<N>+AllocOdd<N>, N:Dim> AllocVersor<N> for T {}

///Picks the buffer to use for an [`Multivector`] of dimension `N`, grade `G`, and using `Self` as the scalar
pub trait AllocMultivector<N:Dim>: Sized {
    type Buffer: MultivectorStorage<Self,N>;
}

///
/// Marks if a [Blade] of a given dimension and grade is guaranteed to always be [simple](SimpleBlade)
///
/// This trait is implemented for scalars, vectors, psuedovectors, and psuedoscalars by bounding the
/// grade to be 0, 1, N, or N-1.
///
/// It is used in a number of locations to allow for certain operations that are only possible with
/// simple blades, ie mutating `SimpleBlade`s, [projecting](Blade::project) onto a Blade, etc.
///
/// At the moment, the implementation uses `typenum` expressions to determine type eligibility,
/// which may be lead to some provability issues when using generic types, especially
/// for psuedoscalars and psuedovectors. However, once the `#[marker]` feature is stabilized,
/// this can be simplified dramatically and will prevent most issues.
///
pub trait AllocSimpleBlade<N:Dim,G:Dim>: AllocBlade<N,G> {}

impl<T:AllocBlade<N,G>,N:Dim,G:Dim> AllocSimpleBlade<N,G> for T where
    //establish that `N` and `G` are constant numbers
    N: DimName+ToTypenum,
    G: DimName+ToTypenum,

    //establish that we can compare `G` with `1` and `N` with `G+1`
    G::Typenum: Add<U1> + IsLessOrEqual<U1>,
    N::Typenum: IsLessOrEqual<Sum<G::Typenum,U1>>,

    //`or` together the two comparisons
    LeEq<G::Typenum, U1>: BitOr<LeEq<N::Typenum, Sum<G::Typenum,U1>>, Output=True>
{}

impl<T, const N: usize> AllocBlade<Const<N>, Dynamic> for T {
    type Buffer = DynBladeStorage<T, Const<N>, Dynamic>;
}

impl<T, const G: usize> AllocBlade<Dynamic, Const<G>> for T {
    type Buffer = DynBladeStorage<T, Dynamic, Const<G>>;
}

impl<T> AllocBlade<Dynamic, Dynamic> for T {
    type Buffer = DynBladeStorage<T, Dynamic, Dynamic>;
}

impl<T> AllocEven<Dynamic> for T {
    type Buffer = DynEvenStorage<T, Dynamic>;
}

impl<T> AllocOdd<Dynamic> for T {
    type Buffer = DynOddStorage<T, Dynamic>;
}

impl<T> AllocMultivector<Dynamic> for T {
    type Buffer = DynMultivectorStorage<T, Dynamic>;
}

#[inline(always)]
fn uninit_array<T, const L: usize>() -> [MaybeUninit<T>; L] {
    //TODO: use `MaybeUninit::uninit_array()` when stabilized
    unsafe {
        //the outer MaybeUninit wraps the [MaybeUninit<T>; L] array
        MaybeUninit::uninit().assume_init()
    }
}

#[inline(always)]
fn array_from_iter<T, I: IntoIterator<Item=T>, const L: usize>(iter:I, kind:&str) -> [T;L] {
    //TODO: use `MaybeUninit::uninit_array()` when stabilized
    let mut uninit: [MaybeUninit<T>;L] = uninit_array();

    //fill the array and count how many spaces we actually fill
    let mut count = 0;
    for (i, x) in (0..L).zip(iter) {
        uninit[i] = MaybeUninit::new(x);
        count = i+1;
    }

    //panic if not enough elements
    if count!=L {
        panic!("Not enough elements to fill {}", kind);
    }

    unsafe { <[MaybeUninit<T>;L] as UninitStorage<T>>::assume_init(uninit) }
}

macro_rules! impl_alloc{

    ($n:literal $($N:literal)*; $($G:literal)*; @$cmd:ident $($pairs:tt)*) => {
        impl_alloc!($($N)*; $($G)*; @$cmd $($pairs)* $(($n, $G))*);

        impl_alloc!($n @$cmd);

    };

    //reuse the macro loop to produce tests for the given dimension
    ($N:literal @tests) => {
        assert_eq!(
            std::mem::size_of::<AllocateEven<f32, Const<$N>>>(),
            //this has some weird behavior
            std::mem::size_of::<f32>() * even_elements($N)
        );

        assert_eq!(
            std::mem::size_of::<AllocateOdd<f32, Const<$N>>>(),
            //this has some weird behavior
            std::mem::size_of::<f32>() * odd_elements($N)
        );

        assert_eq!(
            std::mem::size_of::<AllocateMultivector<f32, Const<$N>>>(),
            std::mem::size_of::<f32>() * 2usize.pow($N)
        );
    };

    ($N:literal @impl) => {
        impl<T> AllocEven<Const<$N>> for T {
            type Buffer = [T; even_elements($N)];
        }

        unsafe impl<T> EvenStorage<T, Const<$N>> for [T; even_elements($N) ] {
            fn dim(&self) -> Const<$N> { Const::<$N> }
            fn uninit(_: Const<$N>,) -> Self::Uninit { uninit_array() }
            fn from_iterator<I:IntoIterator<Item=T>>(_: Const<$N>, iter: I) -> Self {
                array_from_iter(iter, "value")
            }
        }

        impl<T> AllocOdd<Const<$N>> for T {
            type Buffer = [T; odd_elements($N)];
        }

        unsafe impl<T> OddStorage<T, Const<$N>> for [T; odd_elements($N) ] {
            fn dim(&self) -> Const<$N> { Const::<$N> }
            fn uninit(_: Const<$N>,) -> Self::Uninit { uninit_array() }
            fn from_iterator<I:IntoIterator<Item=T>>(_: Const<$N>, iter: I) -> Self {
                array_from_iter(iter, "value")
            }
        }

        impl<T> AllocMultivector<Const<$N>> for T {
            type Buffer = [T; 2usize.pow($N)];
        }

        unsafe impl<T> MultivectorStorage<T, Const<$N>> for [T; 2usize.pow($N)] {
            fn dim(&self) -> Const<$N> { Const::<$N> }
            fn uninit(_: Const<$N>,) -> Self::Uninit { uninit_array() }
            fn from_iterator<I:IntoIterator<Item=T>>(_: Const<$N>, iter: I) -> Self {
                array_from_iter(iter, "multivector")
            }
        }

    };

    (; $($_G:literal)*; @impl $(($N:literal, $G:literal))*) => {
        $(
            impl<T> AllocBlade<Const<$N>, Const<$G>> for T {
                type Buffer = [T; binom($N, $G)];
            }

            unsafe impl<T> BladeStorage<T, Const<$N>, Const<$G>> for [T; binom($N, $G)] {
                fn dim(&self) -> Const<$N> { Const::<$N> }
                fn grade(&self) -> Const<$G> { Const::<$G> }

                fn uninit(_: Const<$N>, _: Const<$G>) -> Self::Uninit { uninit_array() }

                fn from_iterator<I:IntoIterator<Item=T>>(_: Const<$N>, _: Const<$G>, iter: I) -> Self {
                    array_from_iter(iter, "blade")
                }
            }

        )*
    };

    //reuse the macro loop to produce tests for the given dimension and grade
    (; $($_G:literal)*; @tests $(($N:literal, $G:literal))*) => {
        $(
            assert_eq!(
                std::mem::size_of::<AllocateBlade<f32, Const<$N>, Const<$G>>>(),
                std::mem::size_of::<f32>() * binom($N, $G)
            );
        )*
    };
}

impl_alloc!(
    0 1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16; 0 1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16; @impl
);

#[test]
#[cfg(test)]
fn buffer_sizes() {
    impl_alloc!(
        0 1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16; 0 1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16; @tests
    );
}
