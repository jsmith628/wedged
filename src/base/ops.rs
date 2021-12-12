
use std::ops::*;
use std::fmt::Debug;
use num_traits::{Zero, One, Inv};

macro_rules! ref_ops {

    ($($RefOp:ident.$ref_fun:ident() = $Op:ident.$fun:ident();)*) => {$(
        pub trait $RefOp<'a,Rhs=Self> {
            type Output;
            fn $ref_fun(&'a self, rhs: Rhs) -> Self::Output;
        }

        impl<'a, T1:?Sized+'a, T2:> $RefOp<'a,T2> for T1 where &'a T1: $Op<T2> {
            type Output = <&'a T1 as $Op<T2>>::Output;
            fn $ref_fun(&'a self, rhs: T2) -> Self::Output {
                self.$fun(rhs)
            }
        }
    )*}

}

ref_ops!(
    RefAdd.ref_add() = Add.add();
    RefSub.ref_sub() = Sub.sub();
    RefMul.ref_mul() = Mul.mul();
    RefDiv.ref_div() = Div.div();
    RefRem.ref_rem() = Rem.rem();
);

pub trait RefNeg<'a> {
    type Output;
    fn ref_neg(&'a self) -> Self::Output;
}

impl<'a, T:'a> RefNeg<'a> for T where &'a T: Neg {
    type Output = <&'a T as Neg>::Output;
    fn ref_neg(&'a self) -> Self::Output { -self }
}

pub trait RefInv<'a> {
    type Output;
    fn ref_inv(&'a self) -> Self::Output;
}

impl<'a, T:'a> RefInv<'a> for T where &'a T: Inv {
    type Output = <&'a T as Inv>::Output;
    fn ref_inv(&'a self) -> Self::Output { self.inv() }
}

macro_rules! all_ref_ops {
    ($($AllRefOp:ident = $RefOp:ident;)*) => {$(
        pub trait $AllRefOp<Rhs:?Sized>: for<'a,'b> $RefOp<'a, &'b Rhs, Output=Self::AllOutput> {
            type AllOutput;
        }
        impl<T1:?Sized,T2:?Sized, U> $AllRefOp<T2> for T1 where T1: for<'a,'b> $RefOp<'a, &'b T2, Output=U> {
            type AllOutput = U;
        }
    )*};
}

all_ref_ops!(
    AllRefAdd = RefAdd;
    AllRefSub = RefSub;
    AllRefMul = RefMul;
    AllRefDiv = RefDiv;
);

pub trait AllRefNeg: for<'a> RefNeg<'a, Output=Self::AllOutput> {
    type AllOutput;
}
impl<T:?Sized, U> AllRefNeg for T where T: for<'a> RefNeg<'a, Output=U> {
    type AllOutput = U;
}

pub trait AllRefInv: for<'a> RefInv<'a, Output=Self::AllOutput> {
    type AllOutput;
}
impl<T:?Sized, U> AllRefInv for T where T: for<'a> RefInv<'a, Output=U> {
    type AllOutput = U;
}

pub trait Scale<Rhs=Self> {
    type Output;
    fn scale(self, rhs:Rhs) -> Self::Output;
}

pub trait InvScale<Rhs=Self> {
    type Output;
    fn inv_scale(self, rhs:Rhs) -> Self::Output;
}

// trace_macros!(true);
auto! {
    pub use na::ClosedAdd;
    pub use na::ClosedSub;
    pub use na::ClosedMul;
    pub use na::ClosedDiv;
    pub trait ClosedNeg = Neg<Output=Self>;
    pub trait ClosedInv = Inv<Output=Self>;

    pub trait ClosedRefAdd = AllRefAdd<Self, AllOutput=Self> + for<'a> Add<&'a Self, Output=Self>;
    pub trait ClosedRefSub = AllRefSub<Self, AllOutput=Self> + for<'a> Sub<&'a Self, Output=Self>;
    pub trait ClosedRefMul = AllRefMul<Self, AllOutput=Self> + for<'a> Mul<&'a Self, Output=Self>;
    pub trait ClosedRefDiv = AllRefDiv<Self, AllOutput=Self> + for<'a> Div<&'a Self, Output=Self>;
    pub trait ClosedRefNeg = AllRefNeg<AllOutput=Self>;
    pub trait ClosedRefInv = AllRefInv<AllOutput=Self>;

    pub trait AddMonoid = Clone + Debug + ClosedAdd + Zero;
    pub trait AddGroup  = AddMonoid     + ClosedSub + ClosedNeg;
    pub trait Ring      = AddGroup      + ClosedMul;
    pub trait UnitRing  = Ring          + One;
    pub trait DivRing   = UnitRing      + ClosedDiv + ClosedInv;

    pub use na::ComplexField;
    pub use na::RealField;

    pub trait RefAddMonoid = AddMonoid + ClosedRefAdd;
    pub trait RefAddGroup  = AddGroup  + RefAddMonoid + ClosedRefSub + ClosedRefNeg;
    pub trait RefRing      = Ring      + RefAddGroup  + ClosedRefMul;
    pub trait RefUnitRing  = UnitRing  + RefRing;
    pub trait RefDivRing   = DivRing   + RefUnitRing  + ClosedRefDiv + ClosedRefInv;

    pub trait RefComplexField = ComplexField + RefDivRing;
    pub trait RefRealField    = RealField    + RefComplexField;

}
// trace_macros!(false);
