//!
//! Helpful traits for grouping together common operations
//!

use std::ops::*;
use std::fmt::Debug;

pub use std::ops::{
    Add, AddAssign, Sub, SubAssign,
    Mul, MulAssign, Div, DivAssign,
    BitXor, BitXorAssign, Rem, RemAssign,
};
pub use num_traits::{Zero, One, Inv};

macro_rules! ref_ops {

    ($($RefOp:ident.$ref_fun:ident() = $Op:ident.$fun:ident(); $name:literal;)*) => {$(

        #[doc = concat!("Does [", $name, "](", stringify!($RefOp), ") using `self` as a reference")]
        ///
        /// The intent is to expose operations between references to generic functions
        /// without needing to have an excessive amount of `where` clauses
        ///
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
    RefAdd.ref_add() = Add.add(); "addition";
    RefSub.ref_sub() = Sub.sub(); "subtraction";
    RefMul.ref_mul() = Mul.mul(); "multiplication";
    RefDiv.ref_div() = Div.div(); "division";
    RefRem.ref_rem() = Rem.rem(); "modulo";
);

/// Does [negation](Neg) using `self` as a reference
///
/// The intent is to expose operations between references to generic functions
/// without needing to have an excessive amount of `where` clauses
///
pub trait RefNeg<'a> {
    type Output;
    fn ref_neg(&'a self) -> Self::Output;
}
impl<'a, T:'a> RefNeg<'a> for T where &'a T: Neg {
    type Output = <&'a T as Neg>::Output;
    fn ref_neg(&'a self) -> Self::Output { -self }
}

/// Finds the multiplicative [inverse](Inv) using `self` as a reference
///
/// The intent is to expose operations between references to generic functions
/// without needing to have an excessive amount of `where` clauses
///
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

        #[doc = concat!("Implemented when [`", stringify!($RefOp), "`] is implmented for all lifetimes")]
        pub trait $AllRefOp<Rhs:>:
            for<'a> $RefOp<'a, Rhs, Output=Self::AllOutput> +
            for<'a,'b> $RefOp<'a, &'b Rhs, Output=Self::AllOutput>
        {
            type AllOutput;
        }
        impl<T1:?Sized,T2:, U> $AllRefOp<T2> for T1 where
            T1: for<'a> $RefOp<'a, T2, Output=U> + for<'a,'b> $RefOp<'a, &'b T2, Output=U>
        {
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

///Implemented when [`RefNeg`] is implemented for all lifetimes
pub trait AllRefNeg: for<'a> RefNeg<'a, Output=Self::AllOutput> {
    type AllOutput;
}
impl<T:?Sized, U> AllRefNeg for T where T: for<'a> RefNeg<'a, Output=U> {
    type AllOutput = U;
}

///Implemented when [`RefInv`] is implemented for all lifetimes
pub trait AllRefInv: for<'a> RefInv<'a, Output=Self::AllOutput> {
    type AllOutput;
}
impl<T:?Sized, U> AllRefInv for T where T: for<'a> RefInv<'a, Output=U> {
    type AllOutput = U;
}

///
/// Additional trait for scalar multiplication
///
/// For most purposes, the `*` operator and `Scale` are exactly the same. However, do to
/// conflicting generic constraints, the `*` operator cannot be implemented on the geometric
/// algebra types for scalar multiplication between two different types of scalars, whereas `Scalar`
/// can.
///
/// The primary use case of this is to allow for interoperability with crates like [`dimensioned`][1]
///
/// [1]: https://crates.io/crates/dimensioned
///
pub trait Scale<Rhs=Self> {
    type Output;
    fn scale(self, rhs:Rhs) -> Self::Output;
}

///
/// Additional trait for scalar division
///
/// For most purposes, the `/` operator and `InvScale` are exactly the same. However, do to
/// conflicting generic constraints, the `/` operator cannot be implemented on the geometric
/// algebra types for scalar division between two different types of scalars, whereas `InvScale`
/// can.
///
/// The primary use case of this is to allow for interoperability with crates like [`dimensioned`][1]
///
/// [1]: https://crates.io/crates/dimensioned
///
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

    ///Trait **alias** for [`Neg`] with a result of type `Self`
    pub trait ClosedNeg = Neg<Output=Self>;
    ///Trait **alias** for [`Inv`] with a result of type `Self`
    pub trait ClosedInv = Inv<Output=Self>;

    /// Trait alias for addition with `&Self`
    pub trait ClosedRefAdd = 'static + Sized + AllRefAdd<Self, AllOutput=Self> + for<'a> Add<&'a Self, Output=Self> + for<'a> AddAssign<&'a Self>;
    /// Trait alias for subtraction with `&Self`
    pub trait ClosedRefSub = 'static + Sized + AllRefSub<Self, AllOutput=Self> + for<'a> Sub<&'a Self, Output=Self> + for<'a> SubAssign<&'a Self>;
    /// Trait alias for multiplication with `&Self`
    pub trait ClosedRefMul = 'static + Sized + AllRefMul<Self, AllOutput=Self> + for<'a> Mul<&'a Self, Output=Self> + for<'a> MulAssign<&'a Self>;
    /// Trait alias for division with `&Self`
    pub trait ClosedRefDiv = 'static + Sized + AllRefDiv<Self, AllOutput=Self> + for<'a> Div<&'a Self, Output=Self> + for<'a> DivAssign<&'a Self>;
    /// Trait alias for negation of `&Self`
    pub trait ClosedRefNeg = 'static + Sized + AllRefNeg<AllOutput=Self>;
    /// Trait alias for multiplicative inversion of `&Self`
    pub trait ClosedRefInv = 'static + Sized + AllRefInv<AllOutput=Self>;

    pub trait AddMonoid = Clone + Debug + ClosedAdd + Zero;
    pub trait AddGroup  = AddMonoid     + ClosedSub + ClosedNeg;
    pub trait MulMonoid = Clone + Debug + ClosedMul + One;
    pub trait MulGroup  = MulMonoid     + ClosedDiv + ClosedInv;
    pub trait Ring      = AddGroup      + ClosedMul;
    pub trait UnitRing  = Ring          + One;
    pub trait DivRing   = UnitRing      + ClosedDiv + ClosedInv;

    pub use na::ComplexField;
    pub use na::RealField;

    pub trait RefAddMonoid = AddMonoid + ClosedRefAdd;
    pub trait RefAddGroup  = AddGroup  + RefAddMonoid + ClosedRefSub + ClosedRefNeg;
    pub trait RefMulMonoid = MulMonoid + ClosedRefMul;
    pub trait RefMulGroup  = MulGroup  + RefMulMonoid + ClosedRefDiv + ClosedRefInv;
    pub trait RefRing      = Ring      + RefAddGroup  + ClosedRefMul;
    pub trait RefUnitRing  = UnitRing  + RefRing;
    pub trait RefDivRing   = DivRing   + RefUnitRing  + ClosedRefDiv + ClosedRefInv;

    pub trait RefComplexField = ComplexField + RefDivRing;
    pub trait RefRealField    = RealField    + RefComplexField;

}
// trace_macros!(false);

//for exponentiation by non-negative ints
pub(crate) fn repeated_doubling<T:ClosedRefMul>(x:T, one:T, p:u32) -> T {

    let mut p = p;
    let mut x = x;
    let mut exp = one;

    while p>0 {
        if p&1 != 0 {
            //if the power is odd, multiply the result by the current base
            exp *= &x;
            p -= 1;
        } else {
            //if the power is even, square the base
            x = x.ref_mul(&x);
            p >>= 1;
        }
    }

    exp

}

//for exponentiation by integers
pub(crate) fn repeated_doubling_inv<T:ClosedRefMul+ClosedInv>(x:T, one:T, p:i32) -> T {

    if p < 0 {
        repeated_doubling(x, one, (-p) as u32)
    } else {
        repeated_doubling(x, one, (-p) as u32).inv()
    }

}
