
use std::mem::MaybeUninit;

use na::base::dimension::{Dim, Const, Dynamic};

use crate::binom;
use crate::storage::{BladeStorage, DynBladeStorage, UninitStorage};

pub type Allocate<T,N,G> = <T as Alloc<N,G>>::Buffer;

pub unsafe trait Alloc<N:Dim,G:Dim>: Sized {
    type Buffer: BladeStorage<Self,N,G>;
}

unsafe impl<T, const N: usize> Alloc<Const<N>, Dynamic> for T {
    type Buffer = DynBladeStorage<T, Const<N>, Dynamic>;
}

unsafe impl<T, const G: usize> Alloc<Dynamic, Const<G>> for T {
    type Buffer = DynBladeStorage<T, Dynamic, Const<G>>;
}

unsafe impl<T> Alloc<Dynamic, Dynamic> for T {
    type Buffer = DynBladeStorage<T, Dynamic, Dynamic>;
}

#[inline(always)]
fn array_from_iter<T, I: IntoIterator<Item=T>, const L: usize>(iter:I, kind:&str) -> [T;L] {
    //TODO: use `MaybeUninit::uninit_array()` when stabilized
    let mut uninit: [MaybeUninit<T>;L] = unsafe {MaybeUninit::uninit().assume_init()};

    //fill the array and count how many spaces we actually fill
    let mut count = 0;
    for (i, x) in (0..L).zip(iter) {
        uninit[i] = MaybeUninit::new(x);
        count = i;
    }

    //panic if not enough elements
    if count+1!=L {
        panic!("Not enough elements to fill {}", kind);
    }

    unsafe { <[MaybeUninit<T>;L] as UninitStorage<T>>::assume_init(uninit) }
}

macro_rules! impl_Alloc {

    ($n:literal $($N:literal)*; $($G:literal)*; $($pairs:tt)*) => {
        impl_Alloc!($($N)*; $($G)*; $($pairs)* $(($n, $G))*);
    };

    (; $($_G:literal)*; @impl $(($N:literal, $G:literal))*) => {
        $(
            unsafe impl<T> Alloc<Const<$N>, Const<$G>> for T {
                type Buffer = [T; binom($N, $G)];
            }

            unsafe impl<T> BladeStorage<T, Const<$N>, Const<$G>> for [T; binom($N, $G)] {
                fn dim(&self) -> Const<$N> { Const::<$N> }
                fn grade(&self) -> Const<$G> { Const::<$G> }

                fn uninit(_: Const<$N>, _: Const<$G>) -> Self::Uninit {
                    //TODO: use `MaybeUninit::uninit_array()` when stabilized
                    unsafe {
                        //the outer MaybeUninit wraps the [MaybeUninit<T>; L] array
                        MaybeUninit::uninit().assume_init()
                    }
                }

                fn from_iterator<I:IntoIterator<Item=T>>(_: Const<$N>, _: Const<$G>, iter: I) -> Self {
                    array_from_iter(iter, "Blade")
                }
            }

        )*
    };

    (; $($_G:literal)*; @tests $(($N:literal, $G:literal))*) => {
        $(
            assert_eq!(
                std::mem::size_of::<Allocate<f32, Const<$N>, Const<$G>>>(),
                std::mem::size_of::<f32>() * binom($N, $G)
            );
        )*
    };
}

impl_Alloc!(
    0 1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16; 0 1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16; @impl
);

#[test]
#[cfg(test)]
fn buffer_sizes() {
    impl_Alloc!(
        0 1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16; 0 1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16; @tests
    );
}
