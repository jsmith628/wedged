
use super::*;

pub type AllocateBlade<T,N,G> = <T as AllocBlade<N,G>>::Buffer;
pub type AllocateEven<T,N> = <T as AllocEven<N>>::Buffer;
pub type AllocateOdd<T,N> = <T as AllocOdd<N>>::Buffer;
pub type AllocateMultivector<T,N> = <T as AllocMultivector<N>>::Buffer;

pub unsafe trait AllocBlade<N:Dim,G:Dim>: Sized {
    type Buffer: BladeStorage<Self,N,G>;
}

pub unsafe trait AllocEven<N:Dim>: Sized {
    type Buffer: EvenStorage<Self,N>;
}

pub unsafe trait AllocOdd<N:Dim>: Sized {
    type Buffer: OddStorage<Self,N>;
}

pub unsafe trait AllocMultivector<N:Dim>: Sized {
    type Buffer: MultivectorStorage<Self,N>;
}

unsafe impl<T, const N: usize> AllocBlade<Const<N>, Dynamic> for T {
    type Buffer = DynBladeStorage<T, Const<N>, Dynamic>;
}

unsafe impl<T, const G: usize> AllocBlade<Dynamic, Const<G>> for T {
    type Buffer = DynBladeStorage<T, Dynamic, Const<G>>;
}

unsafe impl<T> AllocBlade<Dynamic, Dynamic> for T {
    type Buffer = DynBladeStorage<T, Dynamic, Dynamic>;
}

unsafe impl<T> AllocEven<Dynamic> for T {
    type Buffer = DynEvenStorage<T, Dynamic>;
}

unsafe impl<T> AllocOdd<Dynamic> for T {
    type Buffer = DynOddStorage<T, Dynamic>;
}

unsafe impl<T> AllocMultivector<Dynamic> for T {
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
    let mut uninit: [MaybeUninit<T>;L] = unsafe {MaybeUninit::uninit().assume_init()};

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

    ($N:literal @tests) => {
        assert_eq!(
            std::mem::size_of::<AllocateEven<f32, Const<$N>>>(),
            //this has some weird behavior
            std::mem::size_of::<f32>() * rotor_elements($N)
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
        unsafe impl<T> AllocEven<Const<$N>> for T {
            type Buffer = [T; rotor_elements($N)];
        }

        unsafe impl<T> EvenStorage<T, Const<$N>> for [T; rotor_elements($N) ] {
            fn dim(&self) -> Const<$N> { Const::<$N> }
            fn uninit(_: Const<$N>,) -> Self::Uninit { uninit_array() }
            fn from_iterator<I:IntoIterator<Item=T>>(_: Const<$N>, iter: I) -> Self {
                array_from_iter(iter, "rotor")
            }
        }

        unsafe impl<T> AllocOdd<Const<$N>> for T {
            type Buffer = [T; odd_elements($N)];
        }

        unsafe impl<T> OddStorage<T, Const<$N>> for [T; odd_elements($N) ] {
            fn dim(&self) -> Const<$N> { Const::<$N> }
            fn uninit(_: Const<$N>,) -> Self::Uninit { uninit_array() }
            fn from_iterator<I:IntoIterator<Item=T>>(_: Const<$N>, iter: I) -> Self {
                array_from_iter(iter, "rotor")
            }
        }

        unsafe impl<T> AllocMultivector<Const<$N>> for T {
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
            unsafe impl<T> AllocBlade<Const<$N>, Const<$G>> for T {
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
