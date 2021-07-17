
use nalgebra::base::dimension::{Dim, Const, Dynamic};

use crate::binom;
use crate::storage::{Storage, DynStorage};

pub type Allocate<T,N,G> = <T as Alloc<N,G>>::Buffer;

pub unsafe trait Alloc<N:Dim,G:Dim>: Clone {
    type Buffer: Storage<Self,N,G>;
}

unsafe impl<T: Clone, const N: usize> Alloc<Const<N>, Dynamic> for T {
    type Buffer = DynStorage<T, Const<N>, Dynamic>;
}

unsafe impl<T: Clone, const G: usize> Alloc<Dynamic, Const<G>> for T {
    type Buffer = DynStorage<T, Dynamic, Const<G>>;
}

unsafe impl<T: Clone> Alloc<Dynamic, Dynamic> for T {
    type Buffer = DynStorage<T, Dynamic, Dynamic>;
}

macro_rules! impl_Alloc {

    ($n:literal $($N:literal)*; $($G:literal)*; $($pairs:tt)*) => {
        impl_Alloc!($($N)*; $($G)*; $($pairs)* $(($n, $G))*);
    };

    (; $($_G:literal)*; @impl $(($N:literal, $G:literal))*) => {
        $(
            unsafe impl<T: Clone> Alloc<Const<$N>, Const<$G>> for T {
                type Buffer = [T; binom($N, $G)];
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
