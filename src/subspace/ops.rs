
use super::*;



macro_rules! maybe_ref {
    ($e:expr; ) => { $e };
    ($e:expr; $a:lifetime) => { &$e };
}

//
// Addition ops
//

macro_rules! impl_add_ops {
    ($Op:ident.$op:ident(); $($a:lifetime)?; $($b:lifetime)?) => {
        impl<$($a,)? $($b,)? T1,T2,U,N:Dim,G:Dim>
            $Op<$(&$b)? SimpleBlade<T2,N,G>> for $(&$a)? SimpleBlade<T1,N,G>
        where
            T1: AllocBlade<N,G>,
            T2: AllocBlade<N,G>,
            U: AllocBlade<N,G>,
            $(&$a)? T1: $Op<$(&$b)? T2, Output=U>,
            Self: MutSimpleBlade
        {
            type Output = SimpleBlade<U,N,G>;
            fn $op(self, rhs: $(&$b)? SimpleBlade<T2,N,G>) -> SimpleBlade<U,N,G> {
                //the `into` here implicitly handles the switch between unwrapping
                //`data` by value or by reference
                SimpleBlade { data: self.data.$op(maybe_ref!(rhs.data; $($b)?)) }
            }
        }
    };

    ($($Op:ident.$op:ident()),*) => {
        $(
            impl_add_ops!($Op.$op();   ;   );
            impl_add_ops!($Op.$op(); 'a;   );
            impl_add_ops!($Op.$op();   ; 'b);
            impl_add_ops!($Op.$op(); 'a; 'b);
        )*
    }
}

macro_rules! impl_add_assign_ops {
    ($Op:ident.$op:ident(); $($a:lifetime)?) => {
        impl<$($a,)? T1,T2,N:Dim,G:Dim> $Op<$(&$a)? SimpleBlade<T2,N,G>> for SimpleBlade<T1,N,G> where
            T1: AllocBlade<N,G> + $Op<$(&$a)? T2>,
            T2: AllocBlade<N,G>,
            Self: MutSimpleBlade
        {
            fn $op(&mut self, rhs: $(&$a)? SimpleBlade<T2,N,G>) {
                self.data.$op(maybe_ref!(rhs.data; $($a)?))
            }
        }
    };

    ($($Op:ident.$op:ident()),*) => {
        $(
            impl_add_assign_ops!($Op.$op();   );
            impl_add_assign_ops!($Op.$op(); 'a);
        )*
    }
}

impl_add_ops!(Add.add(), Sub.sub());
impl_add_assign_ops!(AddAssign.add_assign(), SubAssign.sub_assign());

impl<T,U,N:Dim,G:Dim> Neg for SimpleBlade<T,N,G> where
    T: AllocBlade<N,G> + Neg<Output=U>,
    U: AllocBlade<N,G>
{
    type Output = SimpleBlade<U,N,G>;
    fn neg(self) -> SimpleBlade<U,N,G> { SimpleBlade { data: -self.data } }
}

impl<'a,T,U,N:Dim,G:Dim> Neg for &'a SimpleBlade<T,N,G> where
    T: AllocBlade<N,G>,
    U: AllocBlade<N,G>,
    &'a T: Neg<Output=U>
{
    type Output = SimpleBlade<U,N,G>;
    fn neg(self) -> SimpleBlade<U,N,G> { SimpleBlade { data: -&self.data } }
}

impl<T:AllocBlade<N,G>+Zero, N:DimName, G:DimName> Zero for SimpleBlade<T,N,G> where Self:MutSimpleBlade {
    fn zero() -> Self { Self { data: Blade::zero() } }
    fn is_zero(&self) -> bool { self.data.is_zero() }
}

//
// Wedge and Dot
//

macro_rules! impl_blade_op {
    (
        $Op:ident.$op:ident() where $G1:ident: $DimOp:ident<$G2:ident> == $DimRes:ident;
        $($a:lifetime)?; $($b:lifetime)?
    ) => {

        impl<$($a,)? $($b,)? T1,T2,U,N:Dim,G1:Dim,G2:Dim>
            $Op<$(&$b)? SimpleBlade<T2,N,G2>> for $(&$a)? SimpleBlade<T1,N,G1>
        where
            T1: AllocBlade<N,G1> + RefMul<T2,Output=U>,
            T2: AllocBlade<N,G2>,
            $G1: $DimOp<$G2>,
            $(&$a)? T1: Mul<$(&$b)? T2, Output=U>,
            U: AllocBlade<N,$DimRes<$G1,$G2>> + ClosedAdd + ClosedSub + Neg<Output=U> + Zero
        {
            type Output = SimpleBlade<U,N,$DimRes<$G1,$G2>>;
            fn $op(self, rhs: $(&$b)? SimpleBlade<T2,N,G2>) -> SimpleBlade<U,N,$DimRes<$G1,$G2>> {
                SimpleBlade { data: self.data.$op(maybe_ref!(rhs.data; $($b)?)) }
            }
        }

    };

    ($Op:ident.$op:ident() where $G1:ident: $DimOp:ident<$G2:ident> == $DimRes:ident) => {
        impl_blade_op!($Op.$op() where $G1: $DimOp<$G2> == $DimRes;   ;   );
        impl_blade_op!($Op.$op() where $G1: $DimOp<$G2> == $DimRes; 'a;   );
        impl_blade_op!($Op.$op() where $G1: $DimOp<$G2> == $DimRes;   ; 'b);
        impl_blade_op!($Op.$op() where $G1: $DimOp<$G2> == $DimRes; 'a; 'b);
    }
}

impl_blade_op!(BitXor.bitxor() where G1:DimAdd<G2> == DimSum);
impl_blade_op!(Rem.rem() where G2:DimSymSub<G1> == DimSymDiff);

//
//Scalar multiplication
//

impl<T1:AllocBlade<N,G>+MulAssign<T2>,T2:Clone,N:Dim,G:Dim> MulAssign<T2> for SimpleBlade<T1,N,G> {
    fn mul_assign(&mut self, t2: T2) { self.data *= t2 }
}

impl<T1:AllocBlade<N,G>+DivAssign<T2>,T2:Clone,N:Dim,G:Dim> DivAssign<T2> for SimpleBlade<T1,N,G> {
    fn div_assign(&mut self, t2: T2) { self.data /= t2 }
}

macro_rules! impl_scalar_binops {
    ($Op:ident.$op:ident() with $Scale:ident, $scale:ident(); $($a:lifetime)?) => {

        impl<$($a,)? T1,T2,U,N:Dim,G:Dim> $Op<T2> for $(&$a)? SimpleBlade<T1,N,G> where
            T1: AllocBlade<N,G>,
            T2: Clone,
            U: AllocBlade<N,G>,
            $(&$a)? T1: $Scale<T2, Output=U>
        {
            type Output = SimpleBlade<U,N,G>;
            fn $op(self, rhs: T2) -> SimpleBlade<U,N,G> {
                SimpleBlade { data: self.data.$scale(rhs) }
            }
        }

    };

    ($Op:ident.$op:ident() with $Scale:ident, $scale:ident()) => {
        impl_scalar_binops!($Op.$op() with $Scale, $scale();   );
        impl_scalar_binops!($Op.$op() with $Scale, $scale(); 'a);
    }

}

impl_scalar_binops!(Mul.mul() with Mul, scale());
impl_scalar_binops!(Scale.scale() with Mul, scale());
impl_scalar_binops!(Div.div() with Div, inv_scale());
impl_scalar_binops!(InvScale.inv_scale() with Div, inv_scale());

impl_forward_scalar_binops!(impl<T:AllocBlade,N,G> Mul.mul() for SimpleBlade);
