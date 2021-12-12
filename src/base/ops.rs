
use std::ops::*;

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
    fn ref_neg(&'a self) -> Self::Output {
        -self
    }
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

pub trait Scale<Rhs=Self> {
    type Output;
    fn scale(self, rhs:Rhs) -> Self::Output;
}

pub trait InvScale<Rhs=Self> {
    type Output;
    fn inv_scale(self, rhs:Rhs) -> Self::Output;
}

pub trait AddGroup: na::ClosedAdd + na::ClosedSub + std::ops::Neg<Output=Self> + num_traits::Zero {}
impl<T:na::ClosedAdd + na::ClosedSub + std::ops::Neg<Output=Self> + num_traits::Zero> AddGroup for T {}
