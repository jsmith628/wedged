
use super::*;

//
// Addition ops. Only possible on SimpleBlade's that are scalars, vectors,
// psuedovectors, and psuedoscalars. While it's kinda a pain to implement those exceptions,
// it is rather convenient
//

macro_rules! impl_add_ops {
    ($Op:ident.$op:ident(), $Op2:ident.$op2:ident(); $($a:lifetime)?; $($b:lifetime)?) => {
        impl<$($a,)? $($b,)? T1,T2,U,N:Dim,G:Dim>
            $Op<$(&$b)? SimpleBlade<T2,N,G>> for $(&$a)? SimpleBlade<T1,N,G>
        where
            T1: AllocSimpleBlade<N,G>,
            T2: AllocSimpleBlade<N,G>,
            U: AllocSimpleBlade<N,G>,
            T1: $Op2<$($a, )? $(&$b)? T2, Output=U>,
        {
            type Output = SimpleBlade<U,N,G>;
            fn $op(self, rhs: $(&$b)? SimpleBlade<T2,N,G>) -> SimpleBlade<U,N,G> {
                SimpleBlade { data: self.data.$op2(maybe_ref!(rhs.data; $($b)?)) }
            }
        }
    };

    ($($Op:ident.$op:ident() $Ref:ident.$ref:ident()),*) => {
        $(
            impl_add_ops!($Op.$op(), $Op.$op()  ;   ;   );
            impl_add_ops!($Op.$op(), $Ref.$ref(); 'a;   );
            impl_add_ops!($Op.$op(), $Op.$op()  ;   ; 'b);
            impl_add_ops!($Op.$op(), $Ref.$ref(); 'a; 'b);
        )*
    }
}

macro_rules! impl_add_assign_ops {
    ($Op:ident.$op:ident(); $($a:lifetime)?) => {
        impl<$($a,)? T1,T2,N:Dim,G:Dim> $Op<$(&$a)? SimpleBlade<T2,N,G>> for SimpleBlade<T1,N,G> where
            T1: AllocSimpleBlade<N,G> + $Op<$(&$a)? T2>,
            T2: AllocSimpleBlade<N,G>,
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

impl_add_ops!(Add.add() RefAdd.ref_add(), Sub.sub() RefSub.ref_sub());
impl_add_assign_ops!(AddAssign.add_assign(), SubAssign.sub_assign());

//
//Zero for SimpleBlade.
//

impl<T:AllocSimpleBlade<N,G>+Zero, N:DimName, G:DimName> Zero for SimpleBlade<T,N,G> {
    fn zero() -> Self { Self { data: Blade::zero() } }
    fn is_zero(&self) -> bool { self.data.is_zero() }
    fn set_zero(&mut self) { self.data.set_zero() }
}

//
//Neg
//

macro_rules! impl_neg {
    (impl<T:$Alloc:ident,$($N:ident),*> Neg, $Op2:ident.$fun:ident() for $Ty:ident; $($a:lifetime)?) => {
        impl<$($a,)? T,U,$($N:Dim),*> Neg for $(&$a)? $Ty<T,$($N),*> where
            T: $Alloc<$($N),*>,
            U: $Alloc<$($N),*>,
            T: $Op2<$($a,)? Output=U>
        {
            type Output = $Ty<U,$($N),*>;
            fn neg(self) -> $Ty<U,$($N),*> { $Ty { data: maybe_ref!(self.data; $($a)?).$fun() } }
        }
    };

    (impl<T:$Alloc:ident,$($N:ident),*> Neg for $Ty:ident) => {
        impl_neg!(impl<T:$Alloc,$($N),*> Neg, Neg.neg()       for $Ty;   );
        impl_neg!(impl<T:$Alloc,$($N),*> Neg, RefNeg.ref_neg() for $Ty; 'a);
    }
}

impl_neg!(impl<T:AllocBlade,N,G> Neg for SimpleBlade);
impl_neg!(impl<T:AllocBlade,N,G> Neg for UnitBlade);
impl_neg!(impl<T:AllocEven,N> Neg for Rotor);
impl_neg!(impl<T:AllocOdd,N> Neg for Reflector);

impl<T,U,N:Dim> Neg for Versor<T,N> where
    T: AllocVersor<N>+Neg<Output=U>,
    U: AllocVersor<N>,
{
    type Output = Versor<U,N>;
    fn neg(self) -> Versor<U,N> {
        match self {
            Versor::Even(r) => Versor::Even(-r),
            Versor::Odd(r) => Versor::Odd(-r),
        }
    }
}

impl<'a,T,U,N:Dim> Neg for &'a Versor<T,N> where
    T: AllocVersor<N>,
    U: AllocVersor<N>,
    T: RefNeg<'a, Output=U>
{
    type Output = Versor<U,N>;
    fn neg(self) -> Versor<U,N> {
        match self {
            Versor::Even(r) => Versor::Even(r.ref_neg()),
            Versor::Odd(r) => Versor::Odd(r.ref_neg()),
        }
    }
}

//
// Wedge and Dot
// Unlike for Mul, only works for SimpleBlade, since these ops *can* give a non unit blade
// from units
//

macro_rules! impl_blade_op {
    (
        $Op:ident.$op:ident() where $G1:ident: $DimOp:ident<$G2:ident> == $DimRes:ident;
        $($a:lifetime)?; $($b:lifetime)?
    ) => {

        impl<$($a,)? $($b,)? T1,T2,U,N:Dim,G1:Dim,G2:Dim>
            $Op<$(&$b)? SimpleBlade<T2,N,G2>> for $(&$a)? SimpleBlade<T1,N,G1>
        where
            T1: AllocBlade<N,G1> + AllRefMul<T2,AllOutput=U>,
            T2: AllocBlade<N,G2>,
            $G1: $DimOp<$G2>,
            U: AllocBlade<N,$DimRes<$G1,$G2>> + AddGroup
        {
            type Output = SimpleBlade<U,N,$DimRes<$G1,$G2>>;
            fn $op(self, rhs: $(&$b)? SimpleBlade<T2,N,G2>) -> SimpleBlade<U,N,$DimRes<$G1,$G2>> {
                SimpleBlade { data: maybe_ref!(self.data; $($a)?).$op(maybe_ref!(rhs.data; $($b)?)) }
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
impl_blade_op!(Rem.rem() where G1:DimSymSub<G2> == DimSymDiff);

//
//Scalar multiplication
//

impl<T:AllocBlade<N,G>+MulAssign<T>+Clone,N:Dim,G:Dim> MulAssign<T> for SimpleBlade<T,N,G> {
    fn mul_assign(&mut self, t: T) { self.data *= t }
}

impl<'a, T:AllocBlade<N,G>+MulAssign<&'a T>,N:Dim,G:Dim> MulAssign<&'a T> for SimpleBlade<T,N,G> {
    fn mul_assign(&mut self, t: &'a T) { self.data *= t }
}

impl<T:AllocBlade<N,G>+DivAssign<T>+Clone,N:Dim,G:Dim> DivAssign<T> for SimpleBlade<T,N,G> {
    fn div_assign(&mut self, t: T) { self.data /= t }
}

impl<'a, T:AllocBlade<N,G>+DivAssign<&'a T>,N:Dim,G:Dim> DivAssign<&'a T> for SimpleBlade<T,N,G> {
    fn div_assign(&mut self, t: &'a T) { self.data /= t }
}

macro_rules! impl_scalar_binops {
    ($Op:ident.$op:ident() with $Scale:ident, $scale:ident(); $($a:lifetime)?) => {

        impl<$($a,)? T1,T2,U,N:Dim,G:Dim> $Op<T2> for $(&$a)? SimpleBlade<T1,N,G> where
            T1: AllocBlade<N,G>,
            T2: Clone,
            U: AllocBlade<N,G>,
            T1: $Scale<$($a, )? T2, Output=U>
        {
            type Output = SimpleBlade<U,N,G>;
            fn $op(self, rhs: T2) -> SimpleBlade<U,N,G> {
                SimpleBlade { data: self.data.$scale(rhs) }
            }
        }

    };

    ($Op:ident.$op:ident() with $Scale:ident, $RefScale:ident, $scale:ident()) => {
        impl_scalar_binops!($Op.$op() with $Scale, $scale()   ;   );
        impl_scalar_binops!($Op.$op() with $RefScale, $scale(); 'a);
    }

}

impl_scalar_binops!(Mul.mul() with Mul, RefMul, scale());
impl_scalar_binops!(Scale.scale() with Mul, RefMul, scale());
impl_scalar_binops!(Div.div() with Div, RefDiv, inv_scale());
impl_scalar_binops!(InvScale.inv_scale() with Div, RefDiv, inv_scale());

impl_forward_scalar_binops!(impl<T:AllocBlade,N,G> Mul.mul() for SimpleBlade);

//
// Versor inversion
//

macro_rules! impl_inv {
    (impl<T:$Alloc:ident,$($N:ident),*> Inv for $Ty:ident $(where T:$($where:tt)*)?) => {
        impl<T,$($N:Dim),*> Inv for $Ty<T,$($N),*> where
            T: $Alloc<$($N),*>,
            T: Neg<Output=T> $(+ Clone + $($where)*)?
        {
            type Output = $Ty<T,$($N),*>;
            fn inv(self) -> $Ty<T,$($N),*> { self.inverse() }
        }

        //NOTE: this _probably optimizes away the extra clone in most cases,
        //but we may want to do a better impl of this
        impl<'a,T,$($N:Dim),*> Inv for &'a $Ty<T,$($N),*> where
            T: $Alloc<$($N),*>,
            T: Clone + Neg<Output=T> $(+ $($where)*)?,
            //TODO: remove this when we change the Clone impls
            $Ty<T,$($N),*>: Clone
        {
            type Output = $Ty<T,$($N),*>;
            fn inv(self) -> $Ty<T,$($N),*> { (*self).clone().inverse() }
        }

    };
}

impl_inv!(impl<T:AllocBlade,N,G> Inv for SimpleBlade where T:RefComplexField);
impl_inv!(impl<T:AllocBlade,N,G> Inv for UnitBlade);
impl_inv!(impl<T:AllocEven,N> Inv for Rotor);
impl_inv!(impl<T:AllocOdd,N> Inv for Reflector);
impl_inv!(impl<T:AllocVersor,N> Inv for Versor);

//
// Versor multiplication
//

macro_rules! impl_mul {

    (
        $Ty1:ident<T:$Alloc1:ident, N $(,$G1:ident)*> * $Ty2:ident<T:$Alloc2:ident, N $(,$G2:ident)*> ==
            $Ty3:ident<T:$Alloc3:ident,N>;
        $($a:lifetime)?; $($b:lifetime)?
    ) => {

        impl<$($a,)? $($b,)? T1, T2, U, N:Dim, $($G1:Dim,)* $($G2:Dim),* >
            Mul<$(&$b)? $Ty2<T2,N $(,$G2)*>> for $(&$a)? $Ty1<T1,N $(,$G1)*>
        where
            T1: $Alloc1<N,$($G1),*> + AllRefMul<T2, AllOutput=U>,
            T2: $Alloc2<N,$($G2),*>,
            U: $Alloc3<N> + AddGroup,
        {

            type Output = $Ty3<U,N>;

            fn mul(self, rhs: $(&$b)? $Ty2<T2,N,$($G2)*>) -> $Ty3<U,N> {
                let n = self.dim_generic();
                $Ty3 {
                    data: mul_selected(
                        maybe_ref!(self.data; $($a)?), maybe_ref!(rhs.data; $($b)?), n
                    )
                }
            }

        }

    };

    ($(
        $Ty1:ident<T:$Alloc1:ident,N $(,$G1:ident)*> * $Ty2:ident<T:$Alloc2:ident,N $(,$G2:ident)*> ==
        $Ty3:ident<T:$Alloc3:ident,N>;
    )*) => {
        $(
            impl_mul!($Ty1<T:$Alloc1,N $(,$G1)*> * $Ty2<T:$Alloc2,N $(,$G2)*> == $Ty3<T:$Alloc3,N>;   ;   );
            impl_mul!($Ty1<T:$Alloc1,N $(,$G1)*> * $Ty2<T:$Alloc2,N $(,$G2)*> == $Ty3<T:$Alloc3,N>; 'a;   );
            impl_mul!($Ty1<T:$Alloc1,N $(,$G1)*> * $Ty2<T:$Alloc2,N $(,$G2)*> == $Ty3<T:$Alloc3,N>;   ; 'b);
            impl_mul!($Ty1<T:$Alloc1,N $(,$G1)*> * $Ty2<T:$Alloc2,N $(,$G2)*> == $Ty3<T:$Alloc3,N>; 'a; 'b);
        )*
    };

}

impl_mul!{

    Rotor<T:AllocEven,N>    * Rotor<T:AllocEven,N>    == Rotor<T:AllocEven,N>;
    Rotor<T:AllocEven,N>    * Reflector<T:AllocOdd,N> == Reflector<T:AllocOdd,N>;
    Reflector<T:AllocOdd,N> * Rotor<T:AllocEven,N>    == Reflector<T:AllocOdd,N>;
    Reflector<T:AllocOdd,N> * Reflector<T:AllocOdd,N> == Rotor<T:AllocEven,N>;

}

macro_rules! impl_unit_blade_mul {
    (
        $Ty1:ident<T:$Alloc1:ident, N $(,$G1:ident)*> * $Ty2:ident<T:$Alloc2:ident, N $(,$G2:ident)*>;
        $($a:lifetime)?; $($b:lifetime)?
    ) => {

        //
        //Note: All of these products result in a Versor.
        //Ideally, we'd have some sort of thing that could selectively pick either a Rotor or
        //Reflector, but that gets.... messy. The trait bounds would get a little crazy and
        //honestly it's a little bit easier to work with if the Output type is the same no matter
        //the grade.
        //

        impl<$($a,)? $($b,)? T1, T2, U, N:Dim, $($G1:Dim,)* $($G2:Dim),* >
            Mul<$(&$b)? $Ty2<T2,N $(,$G2)*>> for $(&$a)? $Ty1<T1,N $(,$G1)*>
        where
            T1: $Alloc1<N,$($G1),*> + AllRefMul<T2, AllOutput=U>,
            T2: $Alloc2<N,$($G2),*>,
            U: AllocVersor<N> + AddGroup,
        {

            type Output = Versor<U,N>;

            fn mul(self, rhs: $(&$b)? $Ty2<T2,N,$($G2)*>) -> Versor<U,N> {
                let n = self.dim_generic();

                if self.even() ^ rhs.even() {
                    Versor::Odd(Reflector {
                        data: mul_selected(
                            maybe_ref!(self.data; $($a)?), maybe_ref!(rhs.data; $($b)?), n
                        )
                    })
                } else {
                    Versor::Even(Rotor {
                        data: mul_selected(
                            maybe_ref!(self.data; $($a)?), maybe_ref!(rhs.data; $($b)?), n
                        )
                    })
                }
            }

        }

    };

    ($(
        $Ty1:ident<T:$Alloc1:ident, N $(,$G1:ident)*> * $Ty2:ident<T:$Alloc2:ident, N $(,$G2:ident)*>;
    )*) => {
        $(
            impl_unit_blade_mul!($Ty1<T:$Alloc1,N $(,$G1)*> * $Ty2<T:$Alloc2,N $(,$G2)*>;   ;   );
            impl_unit_blade_mul!($Ty1<T:$Alloc1,N $(,$G1)*> * $Ty2<T:$Alloc2,N $(,$G2)*>; 'a;   );
            impl_unit_blade_mul!($Ty1<T:$Alloc1,N $(,$G1)*> * $Ty2<T:$Alloc2,N $(,$G2)*>;   ; 'b);
            impl_unit_blade_mul!($Ty1<T:$Alloc1,N $(,$G1)*> * $Ty2<T:$Alloc2,N $(,$G2)*>; 'a; 'b);
        )*
    }

}

impl_unit_blade_mul!{
    UnitBlade<T:AllocBlade,N,G1> * UnitBlade<T:AllocBlade,N,G2>;
    UnitBlade<T:AllocBlade,N,G> * Rotor<T:AllocEven,N>;
    UnitBlade<T:AllocBlade,N,G> * Reflector<T:AllocOdd,N>;
    Rotor<T:AllocEven,N>        * UnitBlade<T:AllocBlade,N,G>;
    Reflector<T:AllocOdd,N>     * UnitBlade<T:AllocBlade,N,G>;
}

macro_rules! impl_versor_mul {
    (
        $Ty1:ident<T:$Alloc1:ident, N $(,$G1:ident)*> * $Ty2:ident<T:$Alloc2:ident, N $(,$G2:ident)*>;
        |$self:ident, $rhs:ident, $r:ident| $versor:ident, $even:expr, $odd:expr;
        $($a:lifetime)?; $($b:lifetime)?
    ) => {

        impl<$($a,)? $($b,)? T1, T2, U, N:Dim, $($G1:Dim,)* $($G2:Dim),* >
            Mul<$(&$b)? $Ty2<T2,N $(,$G2)*>> for $(&$a)? $Ty1<T1,N $(,$G1)*>
        where
            T1: $Alloc1<N,$($G1),*> + AllRefMul<T2, AllOutput=U>,
            T2: $Alloc2<N,$($G2),*>,
            U: AllocVersor<N> + AddGroup,
        {

            type Output = Versor<U,N>;

            fn mul($self, $rhs: $(&$b)? $Ty2<T2,N,$($G2)*>) -> Versor<U,N> {
                use Versor::*;
                match $versor {
                    Even($r) => $even,
                    Odd($r) => $odd,
                }
            }

        }

    };

    ($(
        $Ty1:ident<T:$Alloc1:ident, N $(,$G1:ident)*> * $Ty2:ident<T:$Alloc2:ident, N $(,$G2:ident)*>;
        |$self:ident, $rhs:ident, $r:ident| $versor:ident, $even:expr, $odd:expr;
    )*) => {
        $(
            impl_versor_mul!(
                $Ty1<T:$Alloc1,N $(,$G1)*> * $Ty2<T:$Alloc2,N $(,$G2)*>;
                |$self, $rhs, $r| $versor, $even, $odd;;
            );
            impl_versor_mul!(
                $Ty1<T:$Alloc1,N $(,$G1)*> * $Ty2<T:$Alloc2,N $(,$G2)*>;
                |$self, $rhs, $r| $versor, $even, $odd; 'a;
            );
            impl_versor_mul!(
                $Ty1<T:$Alloc1,N $(,$G1)*> * $Ty2<T:$Alloc2,N $(,$G2)*>;
                |$self, $rhs, $r| $versor, $even, $odd; ; 'b
            );
            impl_versor_mul!(
                $Ty1<T:$Alloc1,N $(,$G1)*> * $Ty2<T:$Alloc2,N $(,$G2)*>;
                |$self, $rhs, $r| $versor, $even, $odd; 'a; 'b
            );
        )*
    }
}

impl_versor_mul!{
    Versor<T:AllocVersor,N> * Versor<T:AllocVersor,N>;     |self,rhs,r| self, r*rhs, r*rhs;
    Versor<T:AllocVersor,N> * UnitBlade<T:AllocBlade,N,G>; |self,rhs,r| self, r*rhs, r*rhs;
    Versor<T:AllocVersor,N> * Rotor<T:AllocEven,N>;        |self,rhs,r| self, Even(r*rhs), Odd(r*rhs);
    Versor<T:AllocVersor,N> * Reflector<T:AllocOdd,N>;     |self,rhs,r| self, Odd(r*rhs), Even(r*rhs);

    UnitBlade<T:AllocBlade,N,G> * Versor<T:AllocVersor,N>; |self,rhs,r| rhs, self*r, self*r;
    Rotor<T:AllocEven,N>        * Versor<T:AllocVersor,N>; |self,rhs,r| rhs, Even(self*r), Odd(self*r);
    Reflector<T:AllocOdd,N>     * Versor<T:AllocVersor,N>; |self,rhs,r| rhs, Odd(self*r), Even(self*r);
}

//
// Division
//

macro_rules! impl_div {
    (
        $Ty1:ident<T:$Alloc1:ident, N $(,$G1:ident)*> / $Ty2:ident<T:$Alloc2:ident, N $(,$G2:ident)*> ==
            $Ty3:ident<T:$Alloc3:ident,N>;
        $($a:lifetime)?; $($b:lifetime)?
    ) => {

        impl<$($a,)? $($b,)? T1, T2, U, N:Dim, $($G1:Dim,)* $($G2:Dim),* >
            Div<$(&$b)? $Ty2<T2,N $(,$G2)*>> for $(&$a)? $Ty1<T1,N $(,$G1)*>
        where
            T1: $Alloc1<N,$($G1),*> + AllRefMul<T2, AllOutput=U>,
            T2: $Alloc2<N,$($G2),*> + Clone + Neg<Output=T2>,
            U: $Alloc3<N> + AddGroup,
        {

            type Output = $Ty3<U,N>;

            fn div(self, rhs: $(&$b)? $Ty2<T2,N,$($G2)*>) -> $Ty3<U,N> {
                self * Inv::inv(rhs)
            }

        }

    };

    ($(
        $Ty1:ident<T:$Alloc1:ident,N $(,$G1:ident)*> / $Ty2:ident<T:$Alloc2:ident,N $(,$G2:ident)*> ==
        $Ty3:ident<T:$Alloc3:ident,N>;
    )*) => {
        $(
            impl_div!($Ty1<T:$Alloc1,N $(,$G1)*> / $Ty2<T:$Alloc2,N $(,$G2)*> == $Ty3<T:$Alloc3,N>;   ;   );
            impl_div!($Ty1<T:$Alloc1,N $(,$G1)*> / $Ty2<T:$Alloc2,N $(,$G2)*> == $Ty3<T:$Alloc3,N>; 'a;   );
            impl_div!($Ty1<T:$Alloc1,N $(,$G1)*> / $Ty2<T:$Alloc2,N $(,$G2)*> == $Ty3<T:$Alloc3,N>;   ; 'b);
            impl_div!($Ty1<T:$Alloc1,N $(,$G1)*> / $Ty2<T:$Alloc2,N $(,$G2)*> == $Ty3<T:$Alloc3,N>; 'a; 'b);
        )*
    };
}

impl_div!{

    UnitBlade<T:AllocBlade,N,G1> / UnitBlade<T:AllocBlade,N,G2> == Versor<T:AllocVersor,N>;
    UnitBlade<T:AllocBlade,N,G>  / Rotor<T:AllocEven,N>         == Versor<T:AllocVersor,N>;
    UnitBlade<T:AllocBlade,N,G>  / Reflector<T:AllocOdd,N>      == Versor<T:AllocVersor,N>;
    UnitBlade<T:AllocBlade,N,G>  / Versor<T:AllocVersor,N>      == Versor<T:AllocVersor,N>;

    Rotor<T:AllocEven,N> / UnitBlade<T:AllocBlade,N,G> == Versor<T:AllocVersor,N>;
    Rotor<T:AllocEven,N> / Rotor<T:AllocEven,N>        == Rotor<T:AllocEven,N>;
    Rotor<T:AllocEven,N> / Reflector<T:AllocOdd,N>     == Reflector<T:AllocOdd,N>;
    Rotor<T:AllocEven,N> / Versor<T:AllocVersor,N>     == Versor<T:AllocVersor,N>;

    Reflector<T:AllocOdd,N> / UnitBlade<T:AllocBlade,N,G> == Versor<T:AllocVersor,N>;
    Reflector<T:AllocOdd,N> / Rotor<T:AllocEven,N>        == Reflector<T:AllocOdd,N>;
    Reflector<T:AllocOdd,N> / Reflector<T:AllocOdd,N>     == Rotor<T:AllocEven,N>;
    Reflector<T:AllocOdd,N> / Versor<T:AllocVersor,N>     == Versor<T:AllocVersor,N>;

    Versor<T:AllocVersor,N> / UnitBlade<T:AllocBlade,N,G> == Versor<T:AllocVersor,N>;
    Versor<T:AllocVersor,N> / Rotor<T:AllocEven,N>        == Versor<T:AllocVersor,N>;
    Versor<T:AllocVersor,N> / Reflector<T:AllocOdd,N>     == Versor<T:AllocVersor,N>;
    Versor<T:AllocVersor,N> / Versor<T:AllocVersor,N>     == Versor<T:AllocVersor,N>;

}

//
// Mul and Div assign
//

macro_rules! impl_mul_div_assign {

    (
        $Ty1:ident<T:$Alloc1:ident, N $(,$G1:ident)*> *= $Ty2:ident<T:$Alloc2:ident, N $(,$G2:ident)*>;
        $($b:lifetime)?
    ) => {

        impl<$($b,)? T1, T2, N:Dim, $($G1:Dim,)* $($G2:Dim),* >
            MulAssign<$(&$b)? $Ty2<T2,N $(,$G2)*>> for $Ty1<T1,N $(,$G1)*>
        where
            T1: $Alloc1<N,$($G1),*> + AllRefMul<T2, AllOutput=T1> + AddGroup,
            T2: $Alloc2<N,$($G2),*>,
        {
            fn mul_assign(&mut self, rhs: $(&$b)? $Ty2<T2,N,$($G2)*>) {
                *self = &*self * rhs
            }
        }

        impl<$($b,)? T1, T2, N:Dim, $($G1:Dim,)* $($G2:Dim),* >
            DivAssign<$(&$b)? $Ty2<T2,N $(,$G2)*>> for $Ty1<T1,N $(,$G1)*>
        where
            T1: $Alloc1<N,$($G1),*> + AllRefMul<T2, AllOutput=T1> + AddGroup,
            T2: $Alloc2<N,$($G2),*> + Clone + Neg<Output=T2>,
            for<'b> &'b T1: Mul<T2, Output=T1>
        {
            fn div_assign(&mut self, rhs: $(&$b)? $Ty2<T2,N,$($G2)*>) {
                *self = Div::div(&*self, rhs)
            }
        }

    };

    ($(
        $Ty1:ident<T:$Alloc1:ident,N $(,$G1:ident)*> *= $Ty2:ident<T:$Alloc2:ident,N $(,$G2:ident)*>;
    )*) => {
        $(
            impl_mul_div_assign!($Ty1<T:$Alloc1,N $(,$G1)*> *= $Ty2<T:$Alloc2,N $(,$G2)*>;   );
            impl_mul_div_assign!($Ty1<T:$Alloc1,N $(,$G1)*> *= $Ty2<T:$Alloc2,N $(,$G2)*>; 'a);
        )*
    };

}

impl_mul_div_assign!(

    Rotor<T:AllocEven, N>    *= Rotor<T:AllocEven, N>;
    Reflector<T:AllocOdd, N> *= Rotor<T:AllocEven, N>;

    Versor<T:AllocVersor, N> *= UnitBlade<T:AllocBlade, N, G>;
    Versor<T:AllocVersor, N> *= Rotor<T:AllocEven, N>;
    Versor<T:AllocVersor, N> *= Reflector<T:AllocOdd, N>;
    Versor<T:AllocVersor, N> *= Versor<T:AllocVersor, N>;

);

//
// One
//

impl<T:AllocEven<N>+AddGroup+Mul<Output=T>+AllRefMul<T,AllOutput=T>+One+PartialEq, N:DimName> One for Rotor<T,N> {
    //TODO: maybe optimize with the assumption the norm is one
    //There are _some_ complications with negative signatures, but we should be able to check that
    fn is_one(&self) -> bool { self.data.is_one() }
    fn set_one(&mut self) { self.data.set_one()}
    fn one() -> Self { Rotor { data: Even::one() } }
}

impl<T:AllocEven<N>, N:Dim> Rotor<T,N> {
    pub fn one_generic(n: N) -> Self where T: One+Zero {
        Rotor { data: Even::one_generic(n) }
    }
}

impl<T:AllocEven<Dynamic>> RotorD<T> {
    pub fn one_dyn(n: usize) -> Self where T: One+Zero {
        Self::one_generic(Dynamic::new(n))
    }
}

impl<T:AllocVersor<N>+AddGroup+Mul<Output=T>+AllRefMul<T,AllOutput=T>+One+PartialEq, N:DimName> One for Versor<T,N> {
    fn one() -> Self { Versor::Even(Rotor::one()) }
    fn is_one(&self) -> bool {
        match self {
            Versor::Even(r) => r.is_one(),
            Versor::Odd(_) => false
        }
    }
    fn set_one(&mut self) {
        match self {
            Versor::Even(r) => return r.set_one(),
            Versor::Odd(_) => *self = Self::one()
        }
    }

}

impl<T:AllocVersor<N>, N:Dim> Versor<T,N> {
    pub fn one_generic(n: N) -> Self where T: One+Zero {
        Versor::Even(Rotor::one_generic(n))
    }
}

impl<T:AllocVersor<Dynamic>> VersorD<T> {
    pub fn one_dyn(n: usize) -> Self where T: One+Zero {
        Self::one_generic(Dynamic::new(n))
    }
}

//
// Iterator Ops
//

//only SimpleBlade can be summed
//(note that we don't need the MutSimpleBlade bound since it's implicit when it checks for Add)
impl_fold!(impl<T:AllocBlade,U:AllocBlade,N,G> Sum<SimpleBlade<T,N,G>> for SimpleBlade<U,N,G>);

impl_fold!(impl<T:AllocEven,U:AllocEven,N> Product<Rotor<T,N>> for Rotor<U,N>);
impl_fold!(impl<T:AllocBlade,U:AllocVersor,N,G> Product<UnitBlade<T,N,G>> for Versor<U,N>);
impl_fold!(impl<T:AllocEven,U:AllocVersor,N> Product<Rotor<T,N>> for Versor<U,N>);
impl_fold!(impl<T:AllocOdd,U:AllocVersor,N> Product<Reflector<T,N>> for Versor<U,N>);
impl_fold!(impl<T:AllocVersor,U:AllocVersor,N> Product<Versor<T,N>> for Versor<U,N>);

//
//Integral powers
//

macro_rules! impl_pow {
    ($Ty:ident<T:$Alloc:ident $(,$N:ident)*>) => {
        impl<T:$Alloc<$($N),*>+RefUnitRing $(, $N:Dim)*> $Ty<T $(,$N)*> {

            pub fn powu(self, p:u32) -> Self {
                let n = self.dim_generic();
                repeated_doubling(self, Self::one_generic(n), p)
            }

            pub fn powi(self, p:i32) -> Self {
                let n = self.dim_generic();
                repeated_doubling_inv(self, Self::one_generic(n), p)
            }

        }
    };
}

impl_pow!(Rotor<T:AllocEven,N>);
impl_pow!(Versor<T:AllocVersor,N>);
