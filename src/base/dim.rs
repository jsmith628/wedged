
pub use na::dimension::*;

use std::ops::Sub;
use typenum::{
    Max, Min,
    Diff, Maximum, Minimum
};

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
    type Output: Dim;
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

//we copy paste here to keep the docs looking consistent between this and nalgebra's

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

impl<const A:usize, const B:usize> DimSymSub<Const<B>> for Const<A> where
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
