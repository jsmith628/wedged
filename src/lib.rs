#![feature(trait_alias)]
#![feature(specialization)]
#![feature(trace_macros)]
#![recursion_limit="16384"]

extern crate nalgebra;
extern crate macro_lisp;

use std::ops::*;
use std::borrow::*;

use macro_lisp::*;
use nalgebra::base::dimension::*;
use typenum::{Unsigned};

pub trait Storage<T> = Index<usize, Output=T> + IndexMut<usize> + AsRef<[T]> + AsMut<[T]> + Borrow<[T]> + BorrowMut<[T]>;

pub unsafe trait _StorageFor<N, G>: Sized {
    type Storage: Storage<Self>;
}

unsafe impl<T,N:Dim,G:Dim> _StorageFor<N,G> for T {
    default type Storage = [T;0];
}

macro_rules! to_const {
    ((to_const [])        $($tt:tt)* ) => { eval!({ typenum::U0::USIZE } $($tt)*); };
    ((to_const [1])       $($tt:tt)* ) => { eval!({ typenum::U1::USIZE } $($tt)*); };
    ((to_const [0 1])     $($tt:tt)* ) => { eval!({ typenum::U2::USIZE } $($tt)*); };
    ((to_const [1 1])     $($tt:tt)* ) => { eval!({ typenum::U3::USIZE } $($tt)*); };
    ((to_const [0 0 1])   $($tt:tt)* ) => { eval!({ typenum::U4::USIZE } $($tt)*); };
    ((to_const [1 0 1])   $($tt:tt)* ) => { eval!({ typenum::U5::USIZE } $($tt)*); };
    ((to_const [0 1 1])   $($tt:tt)* ) => { eval!({ typenum::U6::USIZE } $($tt)*); };
    ((to_const [1 1 1])   $($tt:tt)* ) => { eval!({ typenum::U7::USIZE } $($tt)*); };
    ((to_const [0 0 0 1]) $($tt:tt)* ) => { eval!({ typenum::U8::USIZE } $($tt)*); };
    ((to_const [1 0 0 1]) $($tt:tt)* ) => { eval!({ typenum::U9::USIZE } $($tt)*); };
    ((to_const [0 1 0 1]) $($tt:tt)* ) => { eval!({ typenum::U10::USIZE } $($tt)*); };
    ((to_const [1 1 0 1]) $($tt:tt)* ) => { eval!({ typenum::U11::USIZE } $($tt)*); };
    ((to_const [0 0 1 1]) $($tt:tt)* ) => { eval!({ typenum::U12::USIZE } $($tt)*); };
    ((to_const [1 0 1 1]) $($tt:tt)* ) => { eval!({ typenum::U13::USIZE } $($tt)*); };
    ((to_const [0 1 1 1]) $($tt:tt)* ) => { eval!({ typenum::U14::USIZE } $($tt)*); };
    ((to_const [1 1 1 1]) $($tt:tt)* ) => { eval!({ typenum::U15::USIZE } $($tt)*); };
}

lisp!(

    //implements _StorageFor for the given constants
    //NOTE: n and k need to be expressions. This is in order to make this impl more readible in
    //the docs
    (defun $impl_storage(n k bin)
        (quote
            unsafe impl<T> _StorageFor<Const<$n>, Const<$k>> for T {
                type Storage = [T; {lisp!((expr $bin))}];
            }
        )
    )

    //starts a loop over a row of Pascal's triangle
    (defun $storage(n call) (impl_storage_loop $n [] $n [1] $call))

    //does the primary loop over k in a row of Pascal's triangle
    (defun $impl_storage_loop(n k nk bin call)

        //run the callback for this value
        ($call (to_const $n) (to_const $k) $bin)

        //loop until n-k is 0
        (if (= [] $nk)
            (quote)
            (impl_storage_step $n (+ $k [1]) $nk $bin $call)
        )

    )

    //steps to the next value in the row of pascal's triangle
    (defun $impl_storage_step(n k nk bin call)
        (impl_storage_loop $n $k (- $nk [1]) (/ (* $bin $nk) $k) $call)
    )

    //loops through the first 2^c rows of pascal's triangle
    (defun $bin_loop(c n call)
        (if (= $c [])

            //loop over the row of pascal's triangle
            (storage $n $call)

            //doing this lowers the recursion depth compared to simple iteration
            //if we don't do this, the compiler's stack overflows :(
            (quote
                lisp!((bin_loop (- $c [1]) (>> $n) $call) );
                lisp!((bin_loop (- $c [1]) (+ (>> $n) [1]) $call) );
            )

        )
    )

    (bin_loop [0 0 1] [] impl_storage)
);

#[test]
fn binom() {

    lisp!(

        (quote

            //finds the binomial coefficient in Rust
            fn binom(n:usize, k:usize) -> usize {
                let mut binom = 1;
                for i in 0..k {
                    binom *= n-i;
                    binom /= i+1;
                }
                binom
            }

        )

        (defun $print_storage(n k bin)
            (quote
                //test that the rust and lisp code agree
                let (n, k, bin) = ($n, $k, lisp!((expr $bin)));
                assert_eq!(bin, binom(n, k));

                //print a pretty triangle :3
                if k==0 { print!("{:2}:", n); }
                print!("{:5}", bin);
                if n==k { println!(); }
            )
        )

        (bin_loop [0 0 1] [] print_storage)
    );

}


pub type StorageOf<T,N,G> = <T as _StorageFor<N,G>>::Storage;


pub struct Blade<T, N: Dim, G: Dim> {
    pub data: StorageOf<T,N,G>
}

impl<T,N:Dim,G1:Dim,G2:Dim> BitXor<Blade<T,N,G2>> for Blade<T,N,G1> where
    T:Mul<T,Output=T>, G1:DimAdd<G2>, DimSum<G1, G2>: Dim
{
    type Output = Blade<T,N,DimSum<G1, G2>>;
    fn bitxor(self, rhs: Blade<T,N,G2>) -> Self::Output { unimplemented!() }
}
