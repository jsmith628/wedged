
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

impl<T:AllocBlade<N,U2>+RefRealField, N:Dim> SimpleBiVecN<T, N> {
    pub fn exp(self) -> Rotor<T,N> where T:AllocEven<N> {
        Rotor::from_inner_unchecked(self.into_inner().exp_even_simple())
    }
}

impl<T:AllocEven<N>, N:Dim> Rotor<T,N> {

    pub fn one_generic(n: N) -> Self where T: One+Zero {
        Rotor { data: Even::one_generic(n) }
    }

    pub fn from_scaled_plane(plane: SimpleBiVecN<T, N>) -> Self where
        T: AllocBlade<N,U2> + RefRealField
    {
        let two = T::one() + T::one();
        (plane/two).exp()
    }

    pub fn from_plane_angle(plane: UnitBiVecN<T, N>, angle: T) -> Self where
        T: AllocBlade<N,U2> + RefRealField
    {

        //get both the sine and cosine of half the angle
        let two = T::one() + T::one();
        let (s, c) = (angle/two).sin_cos();

        //create an even of the form `cos(angle) + plane*sin(angle)`
        let mut r = Even::from(plane.into_inner() * s);
        r[0] = c;

        //return
        Self::from_inner_unchecked(r)

    }

    pub fn rot<'a,M>(&'a self, m:M) -> <&'a Self as VersorMul<M>>::Output where &'a Self: VersorMul<M> {
        self.versor_mul(m)
    }

    pub fn log(self) -> BiVecN<T,N> where T: AllocBlade<N,U2> + RefRealField {
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

}

impl<T:AllocEven<Dynamic>> RotorD<T> {

    pub fn one_dyn(n: usize) -> Rotor<T,Dynamic> where T: One+Zero {
        Self::one_generic(Dynamic::new(n))
    }

}

impl<T:AllocEven<U2>+RefRealField> Rotor2<T> {
    pub fn from_angle(angle:T) -> Self
    {
        let two = T::one() + T::one();
        let (s, c) = (angle/two).sin_cos();
        Self::from_inner_unchecked(Even2::new(c, s))
    }

    fn get_half_angle(&self) -> T where T:RefRealField {
        self.im.clone().atan2(self.re.clone())
    }

    pub fn get_angle(&self) -> T where T:RefRealField {
        self.get_half_angle() * (T::one() + T::one())
    }

}

impl<T:AllocEven<U2>+RefRealField> Rotor3<T> {
    pub fn from_scaled_axis(scaled_axis: Vec3<T>) -> Self
    {
        //TODO: make sure this is actually undual and not dual
        Self::from_scaled_plane(scaled_axis.undual().into())
    }

    pub fn from_axis_angle(axis:UnitVec3<T>, angle:T) -> Self
    {
        Self::from_plane_angle(UnitBiVec3::from_inner_unchecked(axis.into_inner().undual()), angle)
    }

    fn get_half_plane_angle(self) -> Option<(UnitBiVec3<T>, T)> {
        let [w, x, y, z] = self.into_inner().data;

        let (c, s) = (w, (x.ref_mul(&x)+y.ref_mul(&y)+z.ref_mul(&z)).sqrt());
        let angle = s.clone().atan2(c);

        if angle.is_zero() {
            None
        } else {
            Some((
                UnitBiVec3::from_inner_unchecked(BiVec3::new(x, y, z)/&s),
                angle
            ))
        }
    }

    fn get_half_scaled_plane(self) -> SimpleBiVec3<T> {
        self.get_half_plane_angle().map_or_else(|| Zero::zero(), |(d, a)| SimpleBiVec3::from(d) * a)
    }

    pub fn get_plane_angle(self) -> Option<(UnitBiVec3<T>, T)> {
        self.get_half_plane_angle().map(|(b,a)| (b, a*(T::one()+T::one())))
    }

    pub fn get_scaled_plane(self) -> SimpleBiVec3<T> {
        self.get_plane_angle().map_or_else(|| Zero::zero(), |(d, a)| SimpleBiVec3::from(d) * a)
    }

}

impl<T:AllocEven<U2>+RefRealField> Rotor4<T> {

    fn get_half_plane_angles(self) -> (Option<(UnitBiVec4<T>, T)>, Option<(UnitBiVec4<T>, T)>) {

        // println!();
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
                return (Some((UnitBiVec4::from_inner_unchecked(b/s), angle)), None);
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

                let [b1, b2, b3, b4, b5, b6] = b.data;

                let dir1 = BiVec4::new(b1,b2,b3,T::zero(),T::zero(),T::zero());
                let dir2 = BiVec4::new(T::zero(),T::zero(),T::zero(),b4,b5,b6);

                // println!("{:+}, {:+}", dir1, dir2);

                (
                    Some((UnitBlade::from_inner_unchecked(dir1), angle1)),
                    Some((UnitBlade::from_inner_unchecked(dir2), angle2)),
                )

            },

            (None, Some(b)) => {

                // println!("{:+}", b);

                let [b1, b2, b3, b4, b5, b6] = b.data;

                let dir1 = BiVec4::new(b1,b2,b3,T::zero(),T::zero(),T::zero());
                let dir2 = -BiVec4::new(T::zero(),T::zero(),T::zero(),b4,b5,b6);

                // println!("{:+}, {:+}", dir1, dir2);

                (
                    Some((UnitBlade::from_inner_unchecked(dir1), angle1)),
                    Some((UnitBlade::from_inner_unchecked(dir2), angle2)),
                )

            },

            (Some(b_plus), Some(b_minus)) => {

                // println!("{:+}, {:+}", b_plus, b_minus);
                let dir1 = (&b_plus + &b_minus) / &two;
                let dir2 = (b_plus - b_minus) / two;

                // println!("{:+}, {:+}", dir1, dir2);

                (
                    Some((UnitBiVec4::from_inner_unchecked(dir1), angle1)),
                    Some((UnitBiVec4::from_inner_unchecked(dir2), angle2))
                )

            }


        }

    }

    fn get_half_scaled_planes(self) -> (SimpleBiVec4<T>, SimpleBiVec4<T>) {
        let (x1, x2) = self.get_half_plane_angles();
        (
            x1.map_or_else(|| SimpleBiVec4::zeroed(), |(d, a)| d.as_simple_blade() * a),
            x2.map_or_else(|| SimpleBiVec4::zeroed(), |(d, a)| d.as_simple_blade() * a),
        )
    }

    pub fn get_plane_angles(self) -> (Option<(UnitBiVec4<T>, T)>, Option<(UnitBiVec4<T>, T)>) {
        let (x1, x2) = self.get_half_plane_angles();
        (
            x1.map(|(d,a)| (d, a*(T::one()+T::one()))),
            x2.map(|(d,a)| (d, a*(T::one()+T::one()))),
        )
    }

    pub fn get_scaled_planes(self) -> (SimpleBiVec4<T>, SimpleBiVec4<T>) {
        let (x1, x2) = self.get_plane_angles();
        (
            x1.map_or_else(|| SimpleBiVec4::zeroed(), |(d, a)| d.as_simple_blade() * a),
            x2.map_or_else(|| SimpleBiVec4::zeroed(), |(d, a)| d.as_simple_blade() * a),
        )
    }

}


#[cfg(test)]
mod tests {

    use super::*;
    use approx::*;
    use rayon::prelude::*;

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

    #[test]
    fn double_rot_log() {


        for n in 0..=4 {

            let iter = {
                (0..binom(n,2)).into_par_iter()
                .flat_map(|i| (0..binom(n,2)).into_par_iter().map(move |j| (i,j)))
                .flat_map(|(i,j)| (-23i32..23).into_par_iter().map(move |a| (i,j,a)))
                .flat_map(|(i,j,a)| (-23i32..23).into_par_iter().map(move |b| (i,j,a,b)))
            };

            iter.for_each(
                |(i,j,a,b)| {

                    let a = 8.0*a as f64;
                    let b = 8.0*b as f64;

                    if a==b || -a==b || a%180.0==0.0 || b%180.0==0.0 { return; }

                    // println!("\ni={} j={} a={} b={}", i,j,a,b);

                    let b1 = BiVecD::basis(n, i) * a.to_radians();
                    let b2 = BiVecD::basis(n, j) * b.to_radians();
                    let b = b1 + b2;

                    let rot = b.clone().exp_rotor();
                    let log = rot.clone().log();

                    // println!("{}: {} = {}", n, b, rot.log());

                    assert_abs_diff_eq!(rot, log.exp_rotor(), epsilon=1024.0*f64::EPSILON);


                }
            )


        }

    }



}
