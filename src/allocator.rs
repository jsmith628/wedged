
use nalgebra::base::dimension::{Dim, Const, Dynamic};

use crate::binom;
use crate::storage::{Storage, DynStorage};

pub type Allocate<T,N,G> = <DefaultAllocator as Allocator<T,N,G>>::Buffer;

pub struct DefaultAllocator;

pub unsafe trait Allocator<T,N:Dim,G:Dim> {
    type Buffer: Storage<T,N,G>;
}

unsafe impl<T, const N: usize> Allocator<T, Const<N>, Dynamic> for DefaultAllocator {
    type Buffer = DynStorage<T, Const<N>, Dynamic>;
}

unsafe impl<T, const G: usize> Allocator<T, Dynamic, Const<G>> for DefaultAllocator {
    type Buffer = DynStorage<T, Dynamic, Const<G>>;
}

unsafe impl<T> Allocator<T, Dynamic, Dynamic> for DefaultAllocator {
    type Buffer = DynStorage<T, Dynamic, Dynamic>;
}

macro_rules! impl_allocator {

    ($n:literal $($N:literal)*; $($G:literal)*; $($pairs:tt)*) => {
        impl_allocator!($($N)*; $($G)*; $($pairs)* $(($n, $G))*);
    };

    (; $($_G:literal)*; @impl $(($N:literal, $G:literal))*) => {
        $(
            unsafe impl<T> Allocator<T, Const<$N>, Const<$G>> for DefaultAllocator {
                type Buffer = [T; binom($N, $G)];
            }
        )*
    };

    (; $($_G:literal)*; @tests $(($N:literal, $G:literal))*) => {
        $(
            assert_eq!(
                std::mem::size_of::<Allocate<f32, Const<$N>, Const<$G>>>()
                std::mem::size_of::<f32>() * binom($N, $G),
            );
        )*
    }
}

impl_allocator!(
    0 1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16; 0 1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16; @impl
);

#[test]
#[cfg(test)]
fn buffer_sizes() {
    impl_allocator!(
        0 1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16; 0 1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16; @tests
    );
}
