
use super::*;

pub trait VersorMul<Rhs>: Sized {
    type Output;
    fn versor_mul(self, rhs: Rhs) -> Self::Output;
}

macro_rules! impl_versor_mul {

    () => {};

    (
        @impl
        $(&$a:lifetime)? $Ty1:ident<T1:$Alloc1:ident, N $(,$G1:ident)*> *
        $(&$b:lifetime)? $Ty2:ident<T2:$Alloc2:ident, N $(,$G2:ident)*> ;
        $($rest:tt)*
    ) => {

        impl<$($a,)? $($b,)? T1, T2, U, N:Dim $(, $G1:Dim)* $(, $G2:Dim)*>
            VersorMul<$(&$b)? $Ty2<T2,N $(,$G2)?>> for $(&$a)? $Ty1<T1,N $(,$G1)?>
        where
            T1: $Alloc1<N $(,$G1)*> + RefMul<T2, Output=U>,
            T2: $Alloc2<N $(,$G2)*>,
            U: $Alloc2<N $(,$G2)*> + for<'c> Mul<&'c T1, Output=U> + AddGroup,
        {
            type Output = $Ty2<U,N $(,$G2)?>;
            fn versor_mul(self, rhs: $(&$b)? $Ty2<T2,N $(,$G2)?>) -> $Ty2<U,N $(,$G2)?> {
                use crate::algebra::MultivectorSrc;
                let shape = rhs.shape();
                versor_mul_selected(self, rhs, shape)
            }
        }

        impl_versor_mul!($($rest)*);

    };

    (
        $Ty1:ident<T1:$Alloc1:ident, N $(,$G1:ident)*> *
        $Ty2:ident<T2:$Alloc2:ident, N $(,$G2:ident)*> ;
        $($rest:tt)*
    ) => {
        impl_versor_mul!(
            @impl     $Ty1<T1:$Alloc1, N $(,$G1)*> * $Ty2<T2:$Alloc2, N $(,$G2)*>;
            @impl &'a $Ty1<T1:$Alloc1, N $(,$G1)*> * $Ty2<T2:$Alloc2, N $(,$G2)*>;
            @impl     $Ty1<T1:$Alloc1, N $(,$G1)*> * &'b $Ty2<T2:$Alloc2, N $(,$G2)*>;
            @impl &'a $Ty1<T1:$Alloc1, N $(,$G1)*> * &'b $Ty2<T2:$Alloc2, N $(,$G2)*>;
            $($rest)*
        );
    }

}

impl_versor_mul!(
    UnitBlade<T1:AllocBlade,N,G1> * Blade<T2:AllocBlade,N,G2>;
    UnitBlade<T1:AllocBlade,N,G1> * SimpleBlade<T2:AllocBlade,N,G2>;
    UnitBlade<T1:AllocBlade,N,G1> * UnitBlade<T2:AllocBlade,N,G2>;
    UnitBlade<T1:AllocBlade,N,G1> * Even<T2:AllocEven,N>;
    UnitBlade<T1:AllocBlade,N,G1> * Rotor<T2:AllocEven,N>;
    UnitBlade<T1:AllocBlade,N,G1> * Odd<T2:AllocOdd,N>;
    UnitBlade<T1:AllocBlade,N,G1> * Reflector<T2:AllocOdd,N>;
    UnitBlade<T1:AllocBlade,N,G1> * Multivector<T2:AllocMultivector,N>;

    Rotor<T1:AllocEven,N> * Blade<T2:AllocBlade,N,G2>;
    Rotor<T1:AllocEven,N> * SimpleBlade<T2:AllocBlade,N,G2>;
    Rotor<T1:AllocEven,N> * UnitBlade<T2:AllocBlade,N,G2>;
    Rotor<T1:AllocEven,N> * Even<T2:AllocEven,N>;
    Rotor<T1:AllocEven,N> * Rotor<T2:AllocEven,N>;
    Rotor<T1:AllocEven,N> * Odd<T2:AllocOdd,N>;
    Rotor<T1:AllocEven,N> * Reflector<T2:AllocOdd,N>;
    Rotor<T1:AllocEven,N> * Multivector<T2:AllocMultivector,N>;

    Reflector<T1:AllocOdd,N> * Blade<T2:AllocBlade,N,G2>;
    Reflector<T1:AllocOdd,N> * SimpleBlade<T2:AllocBlade,N,G2>;
    Reflector<T1:AllocOdd,N> * UnitBlade<T2:AllocBlade,N,G2>;
    Reflector<T1:AllocOdd,N> * Even<T2:AllocEven,N>;
    Reflector<T1:AllocOdd,N> * Rotor<T2:AllocEven,N>;
    Reflector<T1:AllocOdd,N> * Odd<T2:AllocOdd,N>;
    Reflector<T1:AllocOdd,N> * Reflector<T2:AllocOdd,N>;
    Reflector<T1:AllocOdd,N> * Multivector<T2:AllocMultivector,N>;
);

macro_rules! versor_versor_mul {

    ($Ty:ident<T:$Alloc:ident, N $(,$G:ident)*>; $($a:lifetime)?; $($b:lifetime)?) => {

        impl<$($a,)? $($b,)? T1, T2, U, N:Dim $(, $G:Dim)*>
            VersorMul<$(&$b)? $Ty<T2,N $(,$G)?>> for $(&$a)? Versor<T1,N>
        where
            T1: AllocVersor<N> + RefMul<T2, Output=U>,
            T2: $Alloc<N $(,$G)*>,
            U: $Alloc<N $(,$G)*> + for<'c> Mul<&'c T1, Output=U> + AddGroup,
        {
            type Output = $Ty<U,N $(,$G)?>;
            fn versor_mul(self, rhs: $(&$b)? $Ty<T2,N $(,$G)*>) -> $Ty<U,N $(,$G)*> {
                match self {
                    Versor::Even(r) => r.versor_mul(rhs),
                    Versor::Odd(r) => r.versor_mul(rhs),
                }
            }
        }

    };

    () => {};
    ($Ty:ident<T:$Alloc:ident, N $(,$G:ident)*>; $($rest:tt)*) => {
        versor_versor_mul!($Ty<T:$Alloc, N $(,$G)*>;   ; );
        versor_versor_mul!($Ty<T:$Alloc, N $(,$G)*>; 'a; );
        versor_versor_mul!($Ty<T:$Alloc, N $(,$G)*>;   ; 'b);
        versor_versor_mul!($Ty<T:$Alloc, N $(,$G)*>; 'a; 'b);
        versor_versor_mul!($($rest)*);
    };

}

versor_versor_mul!(
    Blade<T:AllocBlade,N,G>;
    SimpleBlade<T:AllocBlade,N,G>;
    UnitBlade<T:AllocBlade,N,G>;
    Even<T:AllocEven,N>;
    Rotor<T:AllocEven,N>;
    Odd<T:AllocOdd,N>;
    Reflector<T:AllocOdd,N>;
    Multivector<T:AllocMultivector,N>;
);

macro_rules! versor_mul_versor {

    ($Ty:ident<T:$Alloc:ident, N $(,$G:ident)*>; $($a:lifetime)?; $($b:lifetime)?) => {

        impl<$($a,)? $($b,)? T1, T2, U, N:Dim $(, $G:Dim)*>
            VersorMul<$(&$b)? Versor<T2,N>> for $(&$a)? $Ty<T1,N $(,$G)?>
        where
            T1: $Alloc<N $(,$G)*> + RefMul<T2, Output=U>,
            T2: AllocVersor<N>,
            U: AllocVersor<N> + for<'c> Mul<&'c T1, Output=U> + AddGroup,
        {
            type Output = Versor<U,N>;
            fn versor_mul(self, rhs: $(&$b)? Versor<T2,N>) -> Versor<U,N> {
                match rhs {
                    Versor::Even(r) => Versor::Even(self.versor_mul(r)),
                    Versor::Odd(r) => Versor::Odd(self.versor_mul(r)),
                }
            }
        }

    };

    () => {};
    ($Ty:ident<T:$Alloc:ident, N $(,$G:ident)*>; $($rest:tt)*) => {
        versor_mul_versor!($Ty<T:$Alloc, N $(,$G)*>;   ; );
        versor_mul_versor!($Ty<T:$Alloc, N $(,$G)*>; 'a; );
        versor_mul_versor!($Ty<T:$Alloc, N $(,$G)*>;   ; 'b);
        versor_mul_versor!($Ty<T:$Alloc, N $(,$G)*>; 'a; 'b);
        versor_mul_versor!($($rest)*);
    };

}

versor_mul_versor!(
    UnitBlade<T:AllocBlade,N,G>;
    Rotor<T:AllocEven,N>;
    Reflector<T:AllocOdd,N>;
    Versor<T:AllocVersor,N>;
);

impl<T:AllocEven<N>, N:Dim> Rotor<T,N> {

    pub fn one_generic(n: N) -> Self where T: One+Zero {
        Rotor { data: Even::one_generic(n) }
    }

    pub fn from_simple_scaled_plane(plane: SimpleBiVecN<T, N>) -> Self where
        T: AllocBlade<N,U2> + RefMul<T,Output=T> + ComplexField
    {
        let angle = plane.norm();
        if angle.is_zero() {
            Self::one_generic(plane.dim_generic())
        } else {
            Self::from_plane_angle(angle, UnitBlade::from_inner_unchecked((plane/angle).into_inner()))
        }
    }

    pub fn from_plane_angle(angle: T, plane: UnitBiVecN<T, N>) -> Self where
        T: AllocBlade<N,U2> + RefMul<T,Output=T> + ComplexField
    {

        //get both the sine and cosine of the angle
        let (s, c) = angle.sin_cos();

        //create an even of the form `cos(angle) + plane*sin(angle)`
        let mut r = Even::from(plane.into_inner() * s);
        r[0] = c;

        //return
        Self::from_inner_unchecked(r)

    }

    pub fn rot<'a,M>(&'a self, m:M) -> <&'a Self as VersorMul<M>>::Output where &'a Self: VersorMul<M> {
        self.versor_mul(m)
    }

}

impl<T:AllocEven<Dynamic>> RotorD<T> {

    pub fn one_dyn(n: usize) -> Rotor<T,Dynamic> where T: One+Zero {
        Self::one_generic(Dynamic::new(n))
    }

}
