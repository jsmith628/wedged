
pub use na::dimension::*;

use std::ops::{Sub, Mul, Div};
use typenum::{
    Max, Min,
    Diff, Maximum, Minimum
};

use crate::binom;

pub trait DimName: na::dimension::DimName {}
impl<const N: usize> DimName for na::dimension::Const<N> {}

pub type AsTypenum<D> = <D as ToTypenum>::Typenum;
pub type AsConst<D> = <D as ToConst>::Const;

pub type DimSymDiff<D1, D2> = <D1 as DimSymSub<D2>>::Output;
pub type DimNameSymDiff<D1, D2> = <D1 as DimNameSymSub<D2>>::Output;

pub trait DimSymSub<D:Dim>: Dim {
    type Output: Dim;
    fn sym_sub(self, other: D) -> Self::Output;
}

pub trait DimNameSymSub<D: na::dimension::DimName>: na::dimension::DimName {
    type Output: na::dimension::DimName;
    fn sym_sub(self, other: D) -> Self::Output;
}

impl<D:Dim> DimSymSub<D> for Dynamic {
    type Output = Dynamic;
    fn sym_sub(self, other: D) -> Self::Output {
        if self.value() >= other.value() {
            Dynamic::new(self.value()-other.value())
        } else {
            Dynamic::new(other.value()-self.value())
        }
    }
}

impl<D:DimName> DimSymSub<Dynamic> for D {
    type Output = Dynamic;
    fn sym_sub(self, other: Dynamic) -> Self::Output {
        if self.value() >= other.value() {
            Dynamic::new(self.value()-other.value())
        } else {
            Dynamic::new(other.value()-self.value())
        }
    }
}

impl<const A:usize, const B:usize> DimSymSub<Const<B>> for Const<A> where
    Const<A>: DimNameSymSub<Const<B>>,
{
    type Output = DimNameSymDiff<Const<A>, Const<B>>;

    fn sym_sub(self, b: Const<B>) -> Self::Output {
        DimNameSymSub::sym_sub(self, b)
    }

}

impl<const A:usize, const B:usize> DimNameSymSub<Const<B>> for Const<A> where
    Const<A>: ToTypenum,
    Const<B>: ToTypenum,

    AsTypenum<Const<A>>: Max<AsTypenum<Const<B>>>,
    AsTypenum<Const<A>>: Min<AsTypenum<Const<B>>>,
    Maximum<AsTypenum<Const<A>>, AsTypenum<Const<B>>>: Sub<
        Minimum<AsTypenum<Const<A>>, AsTypenum<Const<B>>>
    >,

    Diff<
        Maximum<AsTypenum<Const<A>>, AsTypenum<Const<B>>>,
        Minimum<AsTypenum<Const<A>>, AsTypenum<Const<B>>>
    >: ToConst
{
    type Output = AsConst<Diff<
        Maximum<AsTypenum<Const<A>>, AsTypenum<Const<B>>>,
        Minimum<AsTypenum<Const<A>>, AsTypenum<Const<B>>>
    >>;

    fn sym_sub(self, _: Const<B>) -> Self::Output {
        <Self::Output as na::dimension::DimName>::name()
    }

}

pub type DimBinom<N,K> = <N as DimBinomCoeff<K>>::Output;
pub type DimNameBinom<N,K> = <N as DimNameBinomCoeff<K>>::Output;

pub trait DimBinomCoeff<K:Dim>: Dim {
    type Output: Dim;
    fn binom(self, k: K) -> Self::Output;
}

pub trait DimNameBinomCoeff<K:na::dimension::DimName>: na::dimension::DimName {
    type Output: na::dimension::DimName;
    fn binom(self, k: K) -> Self::Output;
}

impl DimBinomCoeff<Dynamic> for Dynamic {
    type Output = Dynamic;
    fn binom(self, k: Dynamic) -> Dynamic {
        Dynamic::new(binom(self.value(), k.value()))
    }
}

impl<const N:usize> DimBinomCoeff<Dynamic> for Const<N> {
    type Output = Dynamic;
    fn binom(self, k: Dynamic) -> Dynamic {
        Dynamic::new(binom(self.value(), k.value()))
    }
}

impl<const K:usize> DimBinomCoeff<Const<K>> for Dynamic {
    type Output = Dynamic;
    fn binom(self, k: Const<K>) -> Dynamic {
        Dynamic::new(binom(self.value(), k.value()))
    }
}

impl<const N:usize, const K:usize> DimBinomCoeff<Const<K>> for Const<N> where
    Const<N>: DimNameBinomCoeff<Const<K>>
{
    type Output = DimNameBinom<Const<N>,Const<K>>;
    fn binom(self, k: Const<K>) -> Self::Output { DimNameBinomCoeff::binom(self, k) }
}

impl<const N:usize, const K:usize> DimNameBinomCoeff<Const<K>> for Const<N> where
    Const<N>: ToTypenum,
    Const<K>: ToTypenum,
    AsTypenum<Const<N>>: BinomCoeff<AsTypenum<Const<K>>>,
    Binom<AsTypenum<Const<N>>, AsTypenum<Const<K>>>: ToConst
{
    type Output = AsConst<
        Binom<AsTypenum<Const<N>>, AsTypenum<Const<K>>>
    >;
    fn binom(self, _: Const<K>) -> Self::Output {
        <Self::Output as na::dimension::DimName>::name()
    }
}



use self::private::*;

#[doc(hidden)]
pub mod private {

    use super::*;

    use std::ops::Add;

    use typenum::*;
    use typenum::{U0, U1};

    pub trait PrivateNonZero: Unsigned {}
    impl<N:Unsigned,B:Bit> PrivateNonZero for UInt<N,B> {}

    pub type Binom<N,K> = <N as BinomCoeff<K>>::Output;
    pub trait BinomCoeff<K> {
        type Output;
    }

    // binom(0,K) == 0 where K>0
    impl<K:PrivateNonZero,B:Bit> BinomCoeff<UInt<K,B>> for UTerm  where UInt<K,B>: NonZero {
        type Output = U0;
    }

    // We need this as explicitely as possible to guarantee we can prove Scalars have 1 element
    // binom(N,0) == 1
    impl<N:Unsigned> BinomCoeff<UTerm> for N {
        type Output = U1;
    }

    // We need this as explicitely as possible to guarantee we can prove Vectors have N elements
    // binom(N,1) == N
    impl<N> BinomCoeff<UInt<UTerm, B1>> for N {
        type Output = N;
    }

    //Unfortunately, there doesn't seem to be a real way to make sure rustc can prove the number
    //of elements for psuedoscalars and psuedovectors in general with generics. Once we have
    //specialization it may be possible though.

    //
    // In theory, this way of computing this is suuuuper slow ( O(2^N) in fact), but rustc has
    // some form of caching, so this actually ends up working for comparably high values for N
    // (the tests go up to N==31). Hence, we go with this since this is a much simpler
    // encoding of the binomial coefficient and since it handles the N>K case way better than
    // the falling factorial computation.
    //
    // binom(n,k) = binom(n-1, k) + binom(n-1, k-1)
    impl<N,K:PrivateNonZero,B,C> BinomCoeff<UInt<K,C>> for UInt<N,B> where
        UInt<N,B>: Sub<B1>,
        UInt<K,C>: Sub<B1>,
        Sub1<UInt<N,B>>: BinomCoeff<UInt<K,C>>,
        Sub1<UInt<N,B>>: BinomCoeff<Sub1<UInt<K,C>>>,
        Binom<Sub1<UInt<N,B>>, UInt<K,C>>: Add<Binom<Sub1<UInt<N,B>>, Sub1<UInt<K,C>>>>
    {
        type Output = Sum<
            Binom<Sub1<UInt<N,B>>, UInt<K,C>>,
            Binom<Sub1<UInt<N,B>>, Sub1<UInt<K,C>>>
        >;
    }

    #[cfg(test)]
    mod tests {

        use super::*;
        use typenum::{
             U0,  U1,  U2,  U3,  U4,  U5,  U6,  U7,  U8,  U9, U10, U11, U12, U13, U14, U15,
            U16, U17, U18, U19, U20, U21, U22, U23, U24, U25, U26, U27, U28, U29, U30, U31
        };

        #[test]
        fn binom() {

            macro_rules! gen_tests {

                //start the loops
                ($($U:ident)*) => { gen_tests!($($U)*; $($U)*); };

                //end the outer loop
                (; $($Uk:ident)*) => {};

                //for a given n-value, test every combination with the k values
                ($Un:ident; $($Uk:ident)*) => {
                    $(
                        assert_eq!(
                            <Binom::<$Un, $Uk> as ToInt<usize>>::to_int(),
                            crate::binom($Un::to_int(), $Uk::to_int())
                        );

                        // println!(
                        //     "({}, {}) == {} == {}",
                        //     <$Un as ToInt<usize>>::to_int(),
                        //     <$Uk as ToInt<usize>>::to_int(),
                        //     <Binom::<$Un, $Uk> as ToInt<usize>>::to_int(),
                        //     crate::binom($Un::to_int(), $Uk::to_int())
                        // );
                    )*
                };

                //the outer loop
                ($U:ident $($Un:ident)*; $($Uk:ident)*) => {
                        gen_tests!($U; $($Uk)*);
                        gen_tests!($($Un)*; $($Uk)*);
                };

            }

            gen_tests!(
                 U0  U1  U2  U3  U4  U5  U6  U7  U8  U9 U10 U11 U12 U13 U14 U15
                U16 U17 U18 U19 U20 U21 U22 U23 U24 U25 U26 U27 U28 U29 U30 U31
            );

        }

    }

}
