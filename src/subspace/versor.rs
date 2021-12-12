
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
            T1: $Alloc1<N $(,$G1)*> + AllRefMul<T2, AllOutput=U>,
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
            T1: AllocVersor<N> + AllRefMul<T2, AllOutput=U>,
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
            T1: $Alloc<N $(,$G)*> + AllRefMul<T2, AllOutput=U>,
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

    pub fn from_scaled_plane(plane: SimpleBiVecN<T, N>) -> Self where
        T: AllocBlade<N,U2> + RefComplexField
    {
        let (angle, plane) = plane.norm_and_normalize();
        if angle.is_zero() {
            Self::one_generic(plane.dim_generic())
        } else {
            Self::from_plane_angle(plane, angle)
        }
    }

    pub fn from_plane_angle(plane: UnitBiVecN<T, N>, angle: T) -> Self where
        T: AllocBlade<N,U2> + RefComplexField
    {

        //get both the sine and cosine of the angle
        let (s, c) = angle.sin_cos();

        println!("sin({:?}) = {:?}, cos({:?})={:?}", angle, s, angle, c);

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

impl<T:AllocEven<U2>> Rotor2<T> {
    pub fn from_angle(angle:T) -> Self where
        T: AllocBlade<U2,U2> + RefComplexField
    {
        Self::from_plane_angle(UnitBiVec2::unit_psuedoscalar(), angle)
    }
}

#[cfg(test)]
mod tests {

    use super::*;
    use approx::*;

    #[test]
    fn circle_fractions_2d() {

        for n in 1..=360 {

            let rot32 = Rotor2::from_angle(2.0*std::f32::consts::PI / n as f32);
            let rot64 = Rotor2::from_angle(2.0*std::f64::consts::PI / n as f64);

            let mut final_rot32 = Rotor2::<f32>::one();
            let mut final_rot64 = Rotor2::<f64>::one();
            for _ in 0..n {
                final_rot32 *= rot32;
                final_rot64 *= rot64;
            }

            assert_abs_diff_eq!(Rotor2::<f32>::one(), final_rot32, epsilon=0.000015);
            assert_abs_diff_eq!(Rotor2::<f64>::one(), final_rot64, epsilon=0.0000000000002);

        }


    }

}
