
use super::*;

//
//Applying the versor operations
//

///
/// Implemented on versor types in order to apply their transformation to various values
///
/// This is mainly intended as a driver for member fuctions of the different versor types
/// (eg [`Rotor::rot()`], [`Versor::apply()`], etc) and not to be used on its own.
///
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
                versor_mul_selected(self.odd(), self, rhs, shape)
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

macro_rules! impl_non_unit_versor_mul {

    () => {};

    (
        @impl
        $(&$a:lifetime)? $Ty1:ident<T1:$Alloc1:ident, N $(,$G1:ident)*> *
        $(&$b:lifetime)? $Ty2:ident<T2:$Alloc2:ident, N $(,$G2:ident)*>
        $({$($where:tt)*})?;
        $($rest:tt)*
    ) => {

        impl<$($a,)? $($b,)? T1, T2, U, N:Dim $(, $G1:Dim)* $(, $G2:Dim)*>
            VersorMul<$(&$b)? $Ty2<T2,N $(,$G2)?>> for $(&$a)? $Ty1<T1,N $(,$G1)?>
        where
            T1: $Alloc1<N $(,$G1)*> + AllRefMul<T2, AllOutput=U> + AllRefMul<T1, AllOutput=U>,
            T2: $Alloc2<N $(,$G2)*>,
            U: $Alloc2<N $(,$G2)*> + for<'c> Mul<&'c T1, Output=U> + AddGroup,
            U: for<'c> Div<&'c U, Output=U>,
            $($($where)*)?
        {
            type Output = $Ty2<U,N $(,$G2)?>;
            fn versor_mul(self, rhs: $(&$b)? $Ty2<T2,N $(,$G2)?>) -> $Ty2<U,N $(,$G2)?> {
                use crate::algebra::MultivectorSrc;
                let shape = rhs.shape();
                let norm_sqrd = self.norm_sqrd();

                let mut res: Self::Output = versor_mul_selected(self.odd(), self, rhs, shape);
                res = res.inv_scale(&norm_sqrd);
                res
            }
        }

        impl_non_unit_versor_mul!($($rest)*);

    };

    (
        $Ty1:ident<T1:$Alloc1:ident, N $(,$G1:ident)*> *
        $Ty2:ident<T2:$Alloc2:ident, N $(,$G2:ident)*>
        $({$($where:tt)*})?;
        $($rest:tt)*
    ) => {
        impl_non_unit_versor_mul!(
            @impl     $Ty1<T1:$Alloc1, N $(,$G1)*> * $Ty2<T2:$Alloc2, N $(,$G2)*> $({$($where)*})?;
            @impl &'a $Ty1<T1:$Alloc1, N $(,$G1)*> * $Ty2<T2:$Alloc2, N $(,$G2)*> $({$($where)*})?;
            @impl     $Ty1<T1:$Alloc1, N $(,$G1)*> * &'b $Ty2<T2:$Alloc2, N $(,$G2)*> $({$($where)*})?;
            @impl &'a $Ty1<T1:$Alloc1, N $(,$G1)*> * &'b $Ty2<T2:$Alloc2, N $(,$G2)*> $({$($where)*})?;
            $($rest)*
        );
    }

}

impl_non_unit_versor_mul!(
    Blade<T1:AllocSimpleBlade,N,G1> * Blade<T2:AllocBlade,N,G2>;
    Blade<T1:AllocSimpleBlade,N,G1> * SimpleBlade<T2:AllocBlade,N,G2>;
    Blade<T1:AllocSimpleBlade,N,G1> * Even<T2:AllocEven,N>;
    Blade<T1:AllocSimpleBlade,N,G1> * Odd<T2:AllocOdd,N>;
    Blade<T1:AllocSimpleBlade,N,G1> * Multivector<T2:AllocMultivector,N>;

    SimpleBlade<T1:AllocBlade,N,G1> * Blade<T2:AllocBlade,N,G2>;
    SimpleBlade<T1:AllocBlade,N,G1> * SimpleBlade<T2:AllocBlade,N,G2>;
    SimpleBlade<T1:AllocBlade,N,G1> * Even<T2:AllocEven,N>;
    SimpleBlade<T1:AllocBlade,N,G1> * Odd<T2:AllocOdd,N>;
    SimpleBlade<T1:AllocBlade,N,G1> * Multivector<T2:AllocMultivector,N>;

    Even<T1:AllocEven,N> * Blade<T2:AllocBlade,N,G2> {N:ToTypenum, AsTypenum<N>: IsLessOrEqual<U3,Output=True>};
    Even<T1:AllocEven,N> * SimpleBlade<T2:AllocBlade,N,G2> {N:ToTypenum, AsTypenum<N>: IsLessOrEqual<U3,Output=True>};
    Even<T1:AllocEven,N> * Even<T2:AllocEven,N> {N:ToTypenum, AsTypenum<N>: IsLessOrEqual<U3,Output=True>};
    Even<T1:AllocEven,N> * Odd<T2:AllocOdd,N> {N:ToTypenum, AsTypenum<N>: IsLessOrEqual<U3,Output=True>};
    Even<T1:AllocEven,N> * Multivector<T2:AllocMultivector,N> {N:ToTypenum, AsTypenum<N>: IsLessOrEqual<U3,Output=True>};

    Odd<T1:AllocOdd,N> * Blade<T2:AllocBlade,N,G2> {N:ToTypenum, AsTypenum<N>: IsLessOrEqual<U3,Output=True>};
    Odd<T1:AllocOdd,N> * SimpleBlade<T2:AllocBlade,N,G2> {N:ToTypenum, AsTypenum<N>: IsLessOrEqual<U3,Output=True>};
    Odd<T1:AllocOdd,N> * Even<T2:AllocEven,N> {N:ToTypenum, AsTypenum<N>: IsLessOrEqual<U3,Output=True>};
    Odd<T1:AllocOdd,N> * Odd<T2:AllocOdd,N> {N:ToTypenum, AsTypenum<N>: IsLessOrEqual<U3,Output=True>};
    Odd<T1:AllocOdd,N> * Multivector<T2:AllocMultivector,N> {N:ToTypenum, AsTypenum<N>: IsLessOrEqual<U3,Output=True>};
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

impl<T:AllocBlade<N, U1>, N:Dim> VecN<T,N> {
    /// Reflects about `self`
    pub fn reflect<'a,M>(&'a self, m:M) -> <&'a Self as VersorMul<M>>::Output where &'a Self: VersorMul<M> {
        self.versor_mul(m)
    }
}

impl<T:AllocBlade<N, U1>, N:Dim> SimpleVecN<T,N> {
    /// Reflects about `self`
    pub fn reflect<'a,M>(&'a self, m:M) -> <&'a Self as VersorMul<M>>::Output where &'a Self: VersorMul<M> {
        self.versor_mul(m)
    }
}

impl<T:AllocBlade<N, U1>, N:Dim> UnitVecN<T,N> {
    /// Reflects about `self`
    pub fn reflect<'a,M>(&'a self, m:M) -> <&'a Self as VersorMul<M>>::Output where &'a Self: VersorMul<M> {
        self.versor_mul(m)
    }
}

impl<T:AllocEven<N>, N:Dim> Rotor<T,N> {

    /// Rotates the given input by self
    pub fn rot<'a,M>(&'a self, m:M) -> <&'a Self as VersorMul<M>>::Output where &'a Self: VersorMul<M> {
        self.versor_mul(m)
    }

}

impl<T:AllocOdd<N>, N:Dim> Reflector<T,N> {

    /// Applies the reflection and rotations of self
    pub fn apply<'a,M>(&'a self, m:M) -> <&'a Self as VersorMul<M>>::Output where &'a Self: VersorMul<M> {
        self.versor_mul(m)
    }

}

impl<T:AllocVersor<N>, N:Dim> Versor<T,N> {

    /// Applies the reflection and rotations of self
    pub fn apply<'a,M>(&'a self, m:M) -> <&'a Self as VersorMul<M>>::Output where &'a Self: VersorMul<M> {
        self.versor_mul(m)
    }

}

//
//Constructions from bivectors / exp and log
//

impl<T:AllocEven<N>+RefRealField, N:Dim> Rotor<T,N> {

    /// Creates a new `Rotor` rotating in the plane of the input and by the angle given by its [`norm`](Blade::norm())
    pub fn from_scaled_plane(plane: SimpleBiVecN<T,N>) -> Self where
        T: AllocBlade<N,U2>
    {
        let two = T::one() + T::one();
        (plane/two).exp()
    }

    /// Creates a new `Rotor` that rotates in the given plane by the given angle
    pub fn from_plane_angle(plane: UnitBiVecN<T,N>, angle: T) -> Self where
        T: AllocBlade<N,U2>
    {

        //get both the sine and cosine of half the angle
        let two = T::one() + T::one();
        let (s, c) = (angle/two).sin_cos();

        //create an even of the form `cos(angle) + plane*sin(angle)`
        let mut r = Even::from(plane.into_inner() * s);
        r[0] = c;

        //return
        r.into_rotor_unchecked()

    }

    ///
    /// Computes a [bivector](BiVecN) whos [exponential](BiVecN::exp_rotor) is `self`
    ///
    /// The result should be a bivector that is the sum of `floor(N/2)` simple bivectors
    /// with directions and magnitudes corresponding to the planes and angles of the simple rotations
    /// making up this `Rotor`.
    ///
    /// # Uniqueness
    ///
    /// As with other non-real logarithms, the result of this function is not unique:
    ///  - As with complex logarithms, an angle of `2π` can always be added in the direction of
    ///    the output to get a result with the same exponential.
    ///  - When `self == -1` and `N >= 3`, there are infinitely many planes in which
    ///    the rotation could have taken place, so an arbitrary choice is picked.
    ///  - For isoclinic rotations (ie double rotations where both rotations have the same angle),
    ///    the choice of rotation planes is also not unique, so again, an arbitrary choice is picked.
    ///
    pub fn log(self) -> BiVecN<T,N> where T: AllocBlade<N,U2> {
        //oooooooh boy

        //so imma do a bad and have this method available for all rotors even though
        //I don't even know if anyone has a general algorithm for this in all dimensions
        //oops

        let (n, g) = (self.dim_generic(), <U2 as na::dimension::DimName>::name());
        match n.value() {

            //weird edge cases
            0 | 1 => BiVecN::zeroed_generic(n, g),

            //complex numbers
            2 => {
                let angle = self.cast_dim_unchecked::<U2>().get_half_angle();
                BiVec2::new(angle).cast_dim_generic(n)
            },

            //quaternions
            3 => self.cast_dim_unchecked::<U3>().get_half_scaled_plane().into_inner().cast_dim_generic(n),

            //magic
            4 => {
                let (plane1, plane2) = self.cast_dim_unchecked::<U4>().get_half_scaled_planes();
                (plane1.into_inner() + plane2.into_inner()).cast_dim_generic(n)
            }

            //TODO: fill in for 5D. It's basically the same as for 4D but where the quadvector part
            //has more degrees of freedom


            _ => unimplemented!("error: log() currently only implemented up to 4 dimensions")


        }

    }

    ///
    /// Raises this rotor to the power of a real number
    ///
    /// Geometrically, this scales the angles of rotation of this rotor by t.
    ///
    /// More concretely, this is calulated as `x^t == exp(t*log(x))`. As such,
    /// whenever [`log()`](Rotor::log()) makes an arbitrary choice for the rotation plane,
    /// this function does as well.
    ///
    pub fn powf(self, t:T) -> Self where T:AllocBlade<N,U2> {
        (self.log() * t).exp_rotor()
    }

    /// Smoothly interpolates the rotations of `self` and `other`
    ///
    /// Concretely, this is computed as `(other/self)^t * self`
    pub fn slerp(self, other: Self, t:T) -> Self where T:AllocBlade<N,U2> {
        //note that the ordering here is very important
        //the rotations are applied in order from right to left
        (other / &self).powf(t) * self
    }

}

impl<T:AllocEven<U2>+RefRealField> Rotor2<T> {

    /// Creates a 2D rotation from an angle
    pub fn from_angle(angle:T) -> Self
    {
        let two = T::one() + T::one();
        let (s, c) = (angle/two).sin_cos();
        Even2::new(c, s).into_rotor_unchecked()
    }

    /// Returns *half* the angle of this `Rotor`'s rotation
    fn get_half_angle(&self) -> T where T:RefRealField {
        self.im.clone().atan2(self.re.clone())
    }

    /// Returns the angle of this `Rotor`'s rotation
    pub fn get_angle(&self) -> T where T:RefRealField {
        self.get_half_angle() * (T::one() + T::one())
    }

}

impl<T:AllocEven<U2>+RefRealField> Rotor3<T> {

    /// Creates a 3D rotation about the given vector axis where the angle is the norm of the vector
    pub fn from_scaled_axis(scaled_axis: Vec3<T>) -> Self
    {
        //TODO: make sure this is actually undual and not dual
        Self::from_scaled_plane(scaled_axis.undual().into())
    }

    /// Creates a 3D rotation about the given axis with the given angle
    pub fn from_axis_angle(axis:UnitVec3<T>, angle:T) -> Self
    {
        Self::from_plane_angle(axis.undual(), angle)
    }

    fn get_half_plane_angle(self) -> Option<(UnitBiVec3<T>, T)> {
        let [w, x, y, z] = self.into_inner().data;

        let (c, s) = (w, (x.ref_mul(&x)+y.ref_mul(&y)+z.ref_mul(&z)).sqrt());
        let angle = s.clone().atan2(c);

        if angle.is_zero() {
            None
        } else {
            Some((
                (BiVec3::new(x, y, z)/&s).into_unit_unchecked(),
                angle
            ))
        }
    }

    fn get_half_scaled_plane(self) -> SimpleBiVec3<T> {
        self.get_half_plane_angle().map_or_else(|| Zero::zero(), |(d, a)| SimpleBiVec3::from(d) * a)
    }

    /// Returns the plane and angle of rotation or `None` if the angle is 0
    pub fn get_plane_angle(self) -> Option<(UnitBiVec3<T>, T)> {
        self.get_half_plane_angle().map(|(b,a)| (b, a*(T::one()+T::one())))
    }

    /// Returns the plane of rotation scaled by the angle of rotation
    pub fn get_scaled_plane(self) -> SimpleBiVec3<T> {
        self.get_plane_angle().map_or_else(|| Zero::zero(), |(d, a)| SimpleBiVec3::from(d) * a)
    }

    /// Returns the axis and angle of rotation or `None` if the angle is 0
    pub fn get_axis_angle(self) -> Option<(UnitVec3<T>, T)> {
        self.get_half_plane_angle().map(|(b,a)| (b.dual(), a*(T::one()+T::one())))
    }

    /// Returns the axis of rotation scaled by the angle of rotation
    pub fn get_scaled_axis(self) -> Vec3<T> {
        self.get_plane_angle().map_or_else(|| Zero::zero(), |(d, a)| BiVec3::from(d).dual() * a)
    }

}

impl<T:AllocEven<U2>+RefRealField> Rotor4<T> {

    fn get_half_plane_angles(self) -> (Option<(UnitBiVec4<T>, T)>, Option<(UnitBiVec4<T>, T)>) {

        // println!("\nlog");
        // println!("{:+}", self);

        // let to_degrees = T::from_subset(&180.0) / T::pi();

        let two = T::one() + T::one();
        let [s, b1, b2, b3, b4, b5, b6, q] = self.into_inner().data;

        //if this is just a single rotation, we can just do what we would do for 3D rotations
        if q.is_zero() {

            let b = BiVec4::new(b1, b2, b3, b4, b5, b6);

            //the RHS 's' is the "scalar" the LHS 's' is the sin
            let (s, c) = (b.norm(), s);
            let angle = s.clone().atan2(c);

            // println!("{}", angle.clone() * to_degrees);

            if angle.is_zero() {
                return (None, None);
            } else {
                return (Some(((b/s).into_unit_unchecked(), angle)), None);
            }

        }

        //using trig identities, we can find the cosine of the sum and differences of the angles
        let cos_minus = s.ref_add(&q);
        let cos_plus = s - q;

        // println!("{} {}", cos_plus, cos_minus);
        // println!("{}° {}°", cos_plus.clone().acos()*&to_degrees, cos_minus.clone().acos()*&to_degrees);

        //next, we find the dual of the bivector part, this has the effect of swapping the
        //two planes to have the opposite angle
        let b = BiVec4::new(b1, b2, b3, b4, b5, b6);
        let b_dual = b.clone().undual();

        // println!("{:+}, {:+}", b, b_dual);

        //then, by adding and subtracting, we end up with two bivectors,
        //one that has the sine of the angle sum on the sum of the planes
        //and one that has the sine of the angle difference on the difference of the planes
        let b_plus = &b - &b_dual;
        let b_minus = b + b_dual;

        //the sines should come from the norms (divided by sqrt(2))
        let sin_plus = (b_plus.norm_sqrd()/&two).sqrt();
        let sin_minus = (b_minus.norm_sqrd()/&two).sqrt();

        // println!("{} {}", b_plus.norm_sqrd(), b_minus.norm_sqrd());

        //normalize (sorta)
        let b_plus = if sin_plus.is_zero() { None } else { Some(b_plus/&sin_plus) };
        let b_minus = if sin_minus.is_zero() { None } else { Some(b_minus/&sin_minus) };

        // println!("{} {}", sin_plus, sin_minus);
        // println!("{}° {}°", sin_plus.clone().asin()*&to_degrees, sin_minus.clone().asin()*&to_degrees);

        //then, we find the angles using atan2
        let angle_plus = sin_plus.atan2(cos_plus);
        let angle_minus = sin_minus.atan2(cos_minus);

        // println!("{}° {}°", angle_plus.ref_mul(&to_degrees), angle_minus.ref_mul(&to_degrees));

        //finally, solve for the angles and directions
        let angle1 = (angle_plus.ref_add(&angle_minus)) / &two;
        let angle2 = (angle_plus - angle_minus) / &two;
        // println!("{} {} {}", angle1>=angle2, angle1.ref_mul(&to_degrees), angle2.ref_mul(&to_degrees));

        match (b_plus, b_minus) {

            //since this happens when the Quadvec part is nonzero but the bivec part is
            //this corresponds to an invalid rotation, so maybe add a panic??
            (None, None) => (None, None),

            //if we have some an isoclinic rotation (ie the rotation angles are the same)
            //then, we have to solve for the angles and planes differently
            (Some(b), None) => {

                // println!("{:+}", b);

                //
                //since we know the rotation is isoclinic, the plane bivector can be decomposed
                //by literally just splitting the coordinates in half
                //
                //the proof of this basically just boils down to showing that since b is it's own dual
                //the first half equals the second half. Then, just grind through the algebra to
                //show that the geometric product of the first half with the second half only has
                //a quadvector component

                let(dir1, dir2) = b.split_isoclinic();
                // println!("{:+}, {:+}", dir1, dir2);
                (
                    Some((dir1.into_unit_unchecked(), angle1)),
                    Some((dir2.into_unit_unchecked(), angle2)),
                )

            },
            (None, Some(b)) => {
                // println!("{:+}", b);
                let(dir1, dir2) = b.split_isoclinic();
                // println!("{:+}, {:+}", dir1, dir2.ref_neg());
                (
                    Some((dir1.into_unit_unchecked(), angle1)),
                    Some((-dir2.into_unit_unchecked(), angle2)),
                )

            },

            (Some(b_plus), Some(b_minus)) => {

                // println!("{:+}, {:+}", b_plus, b_minus);
                let dir1 = (&b_plus + &b_minus) / &two;
                let dir2 = (b_plus - b_minus) / two;

                // println!("{:+}, {:+}", dir1, dir2);into_iter

                (
                    Some((dir1.into_unit_unchecked(), angle1)),
                    Some((dir2.into_unit_unchecked(), angle2)),
                )

            }


        }

    }

    fn get_half_scaled_planes(self) -> (SimpleBiVec4<T>, SimpleBiVec4<T>) {
        let (x1, x2) = self.get_half_plane_angles();
        (
            x1.map_or_else(|| SimpleBiVec4::zeroed(), |(d, a)| d.into_simple() * a),
            x2.map_or_else(|| SimpleBiVec4::zeroed(), |(d, a)| d.into_simple() * a),
        )
    }

    /// Returns both planes and both angles of rotation or `None` for either if they are 0
    pub fn get_plane_angles(self) -> (Option<(UnitBiVec4<T>, T)>, Option<(UnitBiVec4<T>, T)>) {
        let (x1, x2) = self.get_half_plane_angles();
        (
            x1.map(|(d,a)| (d, a*(T::one()+T::one()))),
            x2.map(|(d,a)| (d, a*(T::one()+T::one()))),
        )
    }

    /// Returns both planes of rotation scaled by their angles of rotation
    pub fn get_scaled_planes(self) -> (SimpleBiVec4<T>, SimpleBiVec4<T>) {
        let (x1, x2) = self.get_plane_angles();
        (
            x1.map_or_else(|| SimpleBiVec4::zeroed(), |(d, a)| d.into_simple() * a),
            x2.map_or_else(|| SimpleBiVec4::zeroed(), |(d, a)| d.into_simple() * a),
        )
    }

}

impl<T:AllocBlade<N,U2>+RefRealField, N:Dim> SimpleBiVecN<T, N> {

    ///
    /// Computes the exponential of this bivector as a [`Rotor`]
    ///
    /// This will produce a `Rotor` that performs a simple rotation in the plane of `self`
    /// by an angle **twice** the norm of `self`
    ///
    /// This is almost always faster than `[BiVecN::exp_rotor()]`, but can only result in
    /// simple rotations.
    ///
    pub fn exp(self) -> Rotor<T,N> where T:AllocEven<N> {
        self.into_inner().exp_even_simple().into_rotor_unchecked()
    }
}

//
//Rotation between vectors
//

impl<T:AllocEven<N>+AllocBlade<N,U1>+RefRealField, N:Dim> Rotor<T,N> {

    #[inline(always)]
    pub fn rot_between_unit(v1:UnitVecN<T,N>, v2: UnitVecN<T,N>) -> Self where
        T: AllocBlade<N,U1>
    { v1.rot_to(v2) }

    #[inline(always)]
    pub fn rot_between_simple(v1:SimpleVecN<T,N>, v2: SimpleVecN<T,N>) -> Self where
        T: AllocBlade<N,U1>
    { v1.rot_to(v2) }

    #[inline(always)]
    pub fn rot_between(v1:VecN<T,N>, v2: VecN<T,N>) -> Self where
        T: AllocBlade<N,U1>
    { v1.rot_to(v2) }

}

impl<T:AllocBlade<N,U1>+RefRealField, N:Dim> UnitVecN<T, N> {
    pub fn rot_to(self, v2: UnitVecN<T,N>) -> Rotor<T,N> where T:AllocEven<N> {

        //In essence, the algorithm is *almost* just v1*v2. However,
        //what this would actually give would be a rotor doing *double* the rotation.
        //so to fix this, we find a vector halfway between v1 and v2 and *then* do the multiplication

        let two = T::one() + T::one();
        let n = self.dim_generic();
        let v2 = (self.as_inner() + v2.into_inner()) / &two;
        let v1 = self;

        //next, we gotta normalize v2
        match v2.into_simple_vec().try_normalize() {
            Some(v2) => {
                //ideally, we'd just do a simple multiplication, and this *does* work,
                //but it requires an extra trait bound, so we're going to do the worse way
                //(v1 * v2).unwrap_even()
                v2.into_blade().mul_even(v1.into_blade()).into_rotor_unchecked()
            },
            None => {
                //if the midpoint is zero, we know the vectors are 180deg apart (so the half angle is 90),
                //but there are infinitely many solutions for the plane.
                //hence... we just pick one!

                //now, in order to do this, we need a plane that includes the given vectors
                //so we first find a basis vector that is not parallel, and then construct a plane
                //going through it and v1

                for i in 0..n.value() {

                    //the way this is done is somewhat suboptimal, but it's kinda necessary
                    //unless we want to add an T:Alloc<N,U2> bound to allow for using ^ instead
                    let ei = Blade::basis_generic(n, v1.grade_generic(), i);
                    let mut plane = v1.as_inner().mul_even(ei);
                    plane[0] = T::zero();

                    if let Some(plane) = plane.try_normalize() {
                        return plane.into_rotor_unchecked();
                    }
                }

                //as a special case if everything is broken:
                panic!("Cannot find rotation between vectors in 1D")
            },
        }

    }
}

impl<T:AllocBlade<N,U1>+RefRealField, N:Dim> SimpleVecN<T, N> {
    #[inline]
    pub fn rot_to(self, v2: SimpleVecN<T,N>) -> Rotor<T,N> where T:AllocEven<N> {
        let n = self.dim_generic();
        match self.try_normalize() {
            None => Rotor::from_inner_unchecked(Even::one_generic(n)),
            Some(v1) => match v2.try_normalize() {
                None => Rotor::from_inner_unchecked(Even::one_generic(n)),
                Some(v2) => v1.rot_to(v2)
            }
        }
    }
}

impl<T:AllocBlade<N,U1>+RefRealField, N:Dim> VecN<T, N> {
    #[inline(always)]
    pub fn rot_to(self, v2: VecN<T,N>) -> Rotor<T,N> where T:AllocEven<N> {
        self.into_simple_unchecked().rot_to(v2.into_simple_unchecked())
    }
}

//
//Reflections
//

impl<T:AllocOdd<N>+Zero, N:Dim> Reflector<T,N> {

    /// Creates a rotation about the hyperplane normal to the given vector
    ///
    /// Concretely, this produces a reflection that flips any components of blades *in* the direction
    /// of the given vector.
    ///
    /// Same as [`Reflector::reflect_unit_normal()`], but performs an extra normalization step
    /// which may be costly in certain contexts
    ///
    pub fn reflect_normal(n: VecN<T,N>) -> Self where T:AllocBlade<N,U1>+RefRealField {
        n.normalize().into_odd().into_reflector_unchecked()
    }

    /// Creates a rotation about the hyperplane normal to the given vector
    ///
    /// Concretely, this produces a reflection that flips any components of blades *in* the direction
    /// of the given vector.
    ///
    /// Same as [`Reflector::reflect_normal()`], but avoids an extra normalization step
    /// which may be costly in certain contexts
    ///
    pub fn reflect_unit_normal(n: UnitVecN<T,N>) -> Self where T:AllocBlade<N,U1> {
        n.into_inner().into_odd().into_reflector_unchecked()
    }

    /// Creates a rotation about the given hyperplane
    ///
    /// Concretely, this produces a reflection that flips any components of blades *perpendicular*
    /// to the given hyperplane
    ///
    /// Same as [`Reflector::reflect_unit_hyperplane()`], but performs an extra normalization step
    /// which may be costly in certain contexts
    ///
    pub fn reflect_hyperplane<G:Dim>(plane: Blade<T,N,G>) -> Self where
        T: AllocBlade<N,G> + AllocBlade<N,U1> + RefRealField,
        N: DimSub<G,Output=U1>
    {
        Self::reflect_normal(plane.dual())
    }

    /// Creates a rotation about the given hyperplane
    ///
    /// Concretely, this produces a reflection that flips any components of blades *perpendicular*
    /// to the given hyperplane
    ///
    /// Same as [`Reflector::reflect_unit_hyperplane()`], but avoids an extra normalization step
    /// which may be costly in certain contexts
    ///
    pub fn reflect_unit_hyperplane<G:Dim>(plane: UnitBlade<T,N,G>) -> Self where
        T: AllocBlade<N,G> + AllocBlade<N,U1> + ClosedNeg,
        N: DimSub<G,Output=U1>
    {
        Self::reflect_unit_normal(plane.dual())
    }

}


#[cfg(test)]
mod tests {

    use super::*;
    use approx::*;
    use rayon::prelude::*;

    use crate::SHORT_TEST_DIM;

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

            assert_abs_diff_eq!(-Rotor2::<f32>::one(), final_rot32, epsilon=0.000015);
            assert_abs_diff_eq!(-Rotor2::<f64>::one(), final_rot64, epsilon=0.0000000000002);

        }


    }

    fn double_rot_iter(n:usize) -> impl ParallelIterator<Item=(usize,usize,f64,f64)> {
        (0..binom(n,2)).into_par_iter()
        .flat_map(|i| (0..=i).into_par_iter().map(move |j| (i,j)))
        .flat_map(|(i,j)| (-45i32..45).into_par_iter().map(move |a| (i,j,a)))
        .flat_map(|(i,j,a)| (-45i32..45).into_par_iter().map(move |b| (i,j,a,b)))
        .map(|(i,j,a,b)| (i,j, (8.0*a as f64).to_radians(), (8.0*b as f64).to_radians()))
    }

    // fn double_rot_iter(n:usize) -> impl Iterator<Item=(usize,usize,f64,f64)> {
    //     (0..binom(n,2)).into_iter()
    //     .flat_map(|i| (0..=i).into_iter().map(move |j| (i,j)))
    //     .flat_map(|(i,j)| (-45i32..45).into_iter().map(move |a| (i,j,a)))
    //     .flat_map(|(i,j,a)| (-45i32..45).into_iter().map(move |b| (i,j,a,b)))
    //     .map(|(i,j,a,b)| (i,j, (8.0*a as f64).to_radians(), (8.0*b as f64).to_radians()))
    // }

    #[test]
    fn double_rot_log() {


        for n in 0..=4 {

            let iter = double_rot_iter(n);

            iter.for_each(
                |(i,j,a,b)| {

                    // if a==b || -a==b || a%180.0==0.0 || b%180.0==0.0 { return; }

                    // println!("\ni={} j={} a={} b={}", i,j,a,b);

                    let b1 = BiVecD::basis(n, i) * a;
                    let b2 = BiVecD::basis(n, j) * b;
                    let b = b1 + b2;

                    let rot = b.clone().exp_rotor();
                    let log = rot.clone().log();

                    // println!("{}: {} = {}", n, b, );

                    assert_abs_diff_eq!(rot, log.exp_rotor(), epsilon=1024.0*f64::EPSILON);


                }
            )


        }

    }

    #[test]
    fn rot_to() {

        for n in 2usize..=4 {

            let s:usize = 3;

            for k in 0..s.pow(2*n as u32) {

                let mut k = k;

                let mut v1 = VecD::zeroed(n);
                for i in 0..n {
                    let (q, r) = (k/s, k%s);
                    v1[i] = r as f64 - (s-1) as f64/2.0;
                    k = q;
                }

                let mut v2 = VecD::zeroed(n);
                for i in 0..n {
                    let (q, r) = (k/s, k%s);
                    v2[i] = r as f64 - (s-1) as f64/2.0;
                    k = q;
                }

                let rot1 = v1.clone().rot_to(v2.clone());
                let rot2 = v2.clone().rot_to(v1.clone());

                if v1.norm_sqrd() == 0.0 || v2.norm_sqrd() == 0.0 {
                    assert_relative_eq!(rot1, Rotor::one_dyn(n));
                    assert_relative_eq!(rot2, Rotor::one_dyn(n));
                } else {
                    assert_relative_eq!(v2.clone().normalize(), rot1.rot(&v1).normalize(), epsilon=1e-10);
                    assert_relative_eq!(v1.clone().normalize(), rot2.rot(&v2).normalize(), epsilon=1e-10);
                }

            }


        }



    }

    #[test]
    fn double_rot_sqrt() {

        for n in 0..=4 {

            let iter = double_rot_iter(n);

            iter.for_each(
                |(i,j,a,b)| {

                    let b1 = BiVecD::basis(n, i) * a;
                    let b2 = BiVecD::basis(n, j) * b;
                    let b = &b1 + &b2;

                    let rot = b.clone().exp_rotor();
                    let sqrt1 = (b/2.0).exp_rotor();
                    let sqrt2 = rot.clone().powf(0.5);

                    let eps = 1024.0*f64::EPSILON;

                    //We cannot directly compare sqrt1 and sqrt2 since they could differ by
                    //a factor of `-1` or some other square root of unity

                    assert_relative_eq!(&sqrt2*&sqrt2, rot, epsilon=eps);
                    assert_relative_eq!(&sqrt1*&sqrt1, rot, epsilon=eps);

                }
            )

        }


    }


    #[test]
    fn basis_reflection() {

        for n in 0..=SHORT_TEST_DIM {

            for i in 0..n {

                //create a reflection about one of the axes
                let normal = VecD::<f64>::basis(n, i)*2.0;
                let unit_normal = normal.clone().into_simple().normalize();
                let r = Reflector::reflect_normal(normal.clone());

                //compute the input and output directly
                let v1 = VecD::from_element(n, 1.0);
                let v2 = VecD::from_index_fn(n, |j| if j==i {-1.0} else {1.0});

                assert_eq!(r.apply(&v1), v2);
                assert_eq!(unit_normal.reflect(&v1), v2);

            }

        }

        dim_name_test_loop!(
            {U1 U2 U3 U4 U5 U6}
            |$N| for i in 0..$N::dim() {

                let normal = VecN::<f64, $N>::basis(i) * 2.0;
                let unit_normal = normal.into_simple().normalize();
                let plane = if $N::dim()<=2 { normal.undual() } else { PsuedoVecN::<f64, $N>::basis(i) };

                let r1 = Reflector::reflect_normal(normal);
                let r2 = Reflector::reflect_hyperplane(plane);

                let v1 = VecN::<_,$N>::from_element(1.0);
                let v2 = VecN::<_,$N>::from_index_fn(|j| if j==i {-1.0} else {1.0});

                assert_eq!(r1, r2);
                assert_eq!(r1.apply(&v1), v2);
                assert_eq!(r2.apply(&v1), v2);
                assert_eq!(normal.reflect(&v1), v2);
                assert_eq!(unit_normal.reflect(&v1), v2);

            }
        );

    }

}
