
use super::*;
use crate::subspace::Rotor;

// #[inline(always)]
pub(crate) fn exp_selected<B1,B2,T:RefRealField,N:Dim>(x:B1, one:B2, epsilon: T::RealField) -> B2 where
    B1: MultivectorSrc<Scalar=T,Item=T,Dim=N>+Clone+DivAssign<T> + Debug,
    for<'a> &'a B1: MultivectorSrc<Scalar=T,Dim=N>,
    B2: MultivectorSrc<Scalar=T,Item=T,Dim=N>+MultivectorDst+Clone+AddAssign+DivAssign<T> + Debug,
    for<'a> &'a B2: MultivectorSrc<Scalar=T,Dim=N>,
{

    //for convenience
    let two = T::one() + T::one();
    let four = T::one() + T::one() + T::one() + T::one();

    //
    //First, we scale down x to have a norm less than one.
    //this is so that we can consistently get within epsilon using the remainder estimation theorem
    //

    let _x = x.clone();

    let mut x = x;
    let mut norm_sqrd = (0..x.elements()).map(|i| x.get(i).ref_mul(x.get(i))).fold(T::zero(), |n,t| n+t);
    let mut factor = T::one();
    let mut halvings = 0;

    //divide the multivector by 2 until the norm is less than one
    while norm_sqrd > T::one() {
        factor /= two.clone();
        x /= two.clone();
        norm_sqrd /= four.clone();
        halvings += 1;
    }

    //we need the shape of the destination in order to use mul_selected
    let shape = one.shape();

    //the necessary size of the next term in order to keep the final result within epsilon of the
    //actual answer. This is a result of Taylor's theorem
    let eps = epsilon * factor;

    //for storing partial results
    let mut exp = one.clone();
    let mut term = one;

    let mut i = T::one();
    let mut remainder = T::e();

    //apply the taylor series for exp() until the remainder term is small enough
    while remainder > eps {

        //compute the next term `x^n / n!`
        term = mul_selected(term, &x, shape);
        term /= i.clone();

        //add the term to the total
        exp += term.clone();

        //increment the index
        i += T::one();

        //update the upper bound for the remainder
        //note that this is in essence the max possible value for the next term
        remainder /= i.clone();

    }

    //finally, each of the halvings we did to the exponent become squarings of the result
    for _ in 0..halvings {
        exp = mul_selected(&exp, &exp, shape);
    }

    // println!("exp({:?}) = {:?}; {}", _x, exp, i);

    exp

}

//yes, this is probably bad, but I don't wanna either write this stuff twice or redesign to make
//it simpler
macro_rules! exp {

    (scalar, $self:ident, $M:ident) => {{
        //a single scalar just gets exp normally
        let n = $self.dim_generic();
        $M::from_iter_generic(n, $self.into_iter().map(|x| x.exp()))
    }};

    (simple, $self:ident, $M:ident) => {{

        let neg = $self.neg_sig();
        let n = $self.dim_generic();
        match $self.try_norm_and_normalize() {
            None => $M::one_generic(n), //if the norm is 0, then exp(self) == 1

            Some((l, b)) => {
                if neg {
                    //negative signatures behave like the exp of complex numbers
                    let (s, c) = l.sin_cos();
                    let mut exp = $M::from_blade(b*s);
                    exp[0] = c;
                    exp
                } else {
                    //positive signatures behave like the exp of split-complex numbers
                    let (s, c) = l.sinh_cosh();
                    let mut exp = $M::from_blade(b*s);
                    exp[0] = c;
                    exp
                }
            },
        }

    }};

    (bivector, $N:ident, $self:ident, $M:ident) => {{

        //using T explicitly here is bad, but we'll fix it later if it's a problem

        let n = $self.dim_generic();
        let (b1, b2) = Blade::<T, $N, U2>::from_iter($self).separate_unit_blades();

        let exp = |(l,b): (T, Blade::<T, $N, U2>)| {
            let (s,c) = l.sin_cos();
            let mut exp = $M::from_blade(b*s);
            exp[0] = c;
            exp
        };

        (b1.map_or_else($M::one, exp) * b2.map_or_else($M::one, exp)).cast_dim_generic(n)

    }}
}

impl<T:RefRealField> BiVec4<T> {

    #[inline(always)]
    pub(crate) fn split_isoclinic(self) -> (Self, Self) {
        let [b1, b2, b3, b4, b5, b6] = self.data;

        (
            BiVec4::new(b1,b2,b3,T::zero(),T::zero(),T::zero()),
            BiVec4::new(T::zero(),T::zero(),T::zero(),b4,b5,b6)
        )
    }

    fn separate_unit_blades(self) -> (Option<(T,BiVec4<T>)>, Option<(T,BiVec4<T>)>) {

        let two = T::one() + T::one();

        let b = self;
        let q = &b^&b;

        // println!("\nexp");
        // println!("{:+}", b);
        // println!("{:+}", q);

        match q.try_normalize() {

            //if q is zero and thus self is already simple
            None => (b.try_norm_and_normalize(), None),

            Some(q) => {

                // println!("{:+}", q);

                let b_dual = &b % q;
                // println!("{:+}", b_dual);

                //taking the undual introduces an extra minus sign, which is why the ops are fliped like that
                let b_plus = &b - &b_dual;
                let b_minus = &b + &b_dual;
                // println!("{:+}, {:+}", b_plus, b_minus);

                let norm_plus = (b_plus.norm_sqrd() / &two).sqrt();
                let norm_minus = (b_minus.norm_sqrd() / &two).sqrt();
                // println!("{:+}, {:+}", norm_plus, norm_minus);

                let l1 = (norm_plus.ref_add(&norm_minus)) / &two;
                let l2 = (norm_plus.ref_sub(&norm_minus)) / &two;
                // println!("{:+}, {:+}", l1, l2);

                let b_plus = if norm_plus.is_zero() { None } else { Some(b_plus / norm_plus) };
                let b_minus = if norm_minus.is_zero() { None } else { Some(b_minus / norm_minus) };

                match (b_plus, b_minus) {
                    (None, None) => (None, None), //not really possible, but whatever

                    //if we have some sort of isoclinic bivector
                    (Some(b), None) | (None, Some(b)) => {
                        let (b1, b2) = b.split_isoclinic();
                        // println!("{:+}, {:+}", b1, b2);
                        (Some((l1, b1)), Some((l2, b2)))
                    },

                    (Some(b_plus), Some(b_minus)) => {
                        let b1 = (&b_plus + &b_minus) / &two;
                        let b2 = (b_plus - b_minus) / &two;
                        // println!("{:+}, {:+}", b1, b2);
                        (Some((l1, b1)), Some((l2, b2)))
                    }
                }

            }
        }




    }

}

impl<T:RefRealField+AllocBlade<N,U2>, N:Dim> BiVecN<T,N> {

    ///
    /// Exponentiates this bivector into a `Rotor`
    ///
    /// In 2D and 3D, this produces a rotation in the plane of this bivector rotated by an angle
    /// *twice* its length.
    ///
    /// In general, a bivector can always be decomposed into the sum of perpendicular simple bivectors,
    /// each of which can be interpreted as a plane with an angle as its length. Then, the
    /// exponential of the sum, is just the the compositions of the simple rotations gotten from
    /// each of the simple bivectors.
    ///
    #[inline]
    pub fn exp_rotor(self) -> Rotor<T,N> where T:AllocEven<N> {
        Rotor::from_inner_unchecked(self.exp_even())
    }

}

impl<T:RefRealField+AllocBlade<N,G>, N:Dim, G:Dim> Blade<T,N,G> {
    #[inline(always)]
    pub(crate) fn exp_simple(self) -> Multivector<T,N> where T:AllocMultivector<N> {
        exp!(simple, self, Multivector)
    }

    #[inline(always)]
    pub(crate) fn exp_even_simple(self) -> Even<T,N> where T:AllocEven<N> {
        if self.even() {
            exp!(simple, self, Even)
        } else {
            let norm = self.norm();
            let mut exp = Even::zeroed_generic(self.dim_generic());
            exp[0] = if self.neg_sig() { norm.cos() } else { norm.cosh() };
            exp
        }
    }
}

impl<T:RefRealField+AllocBlade<N,G>, N:Dim, G:Dim> Blade<T,N,G> {

    ///Computes the exponential of `self` as a multivector
    pub fn exp(self) -> Multivector<T,N> where T:AllocMultivector<N> {

        //match the dimension so we can optimize for the first few dimensions
        let (n, g) = self.shape();

        match (n.value(), g.value()) {
            //scalars do scalar things
            (_, 0) => exp!(scalar, self, Multivector),

            //if we're guaranteed to be simple
            (n, g) if g==1 || g+1>=n => self.exp_simple(),

            //*magic*
            (4, 2) => exp!(bivector, U4, self, Multivector),

            //if not simple, we gotta use the taylor series
            _ => exp_selected(self, Multivector::one_generic(n), T::default_epsilon())
        }

    }


    ///
    /// Computes the exponential of `self` while selecting only the even elements
    ///
    /// For blades of *even* grade, this is equivalent in value to [`Blade::exp`]
    ///
    pub fn exp_even(self) -> Even<T,N> where T:AllocEven<N>, G:DimEven {

        //match the dimension so we can optimize for the first few dimensions
        let (n, g) = self.shape();

        match (n.value(), g.value()) {
            //scalars do scalar things
            (_, 0) => exp!(scalar, self, Even),

            //if we're guaranteed to be simple
            (n, g) if g==1 || g+1>=n => self.exp_even_simple(),

            (4, 2) => exp!(bivector, U4, self, Even),

            //if not simple, we gotta use the taylor series
            _ => exp_selected(self, Even::one_generic(n), T::default_epsilon())
        }

    }

}

//TODO: make work for Dynamic dims
impl<T:RefRealField+AllocEven<N>, N:Dim> Even<T,N> {

    ///Computes the exponential of `self`
    pub fn exp(self) -> Even<T,N> {

        //match the dimension so we can optimize for the first few dimensions
        let n = self.dim_generic();
        match n.value() {

            //a single scalar
            0 | 1 => {
                Self::from_iter_generic(n, self.into_iter().map(|x| x.exp()))
            },

            //complex numbers
            2 => {

                let [a, b] = self.cast_dim::<U2>().data;

                let (s,c) = b.sin_cos();
                Even2::new(c, s) * a.exp()

            }.cast_dim_generic(n.clone()),

            //quaternions
            3 => {

                let [w,x,y,z] = self.cast_dim::<U3>().data;

                let l = x.ref_mul(&x) + y.ref_mul(&y) + z.ref_mul(&z);
                if l.is_zero() { return Even::one_generic(n); }
                let l = l.sqrt();

                let (s,c) = l.clone().sin_cos();
                let s = s/l;
                Even3::new(c, x*&s, y*&s, z*&s) * w.exp()

            }.cast_dim_generic(n),

            //4D rotors
            4 => {

                //this is only possible because of the special formula for bivectors in 4D and 5D
                //and because the quadvector part is guaranteed to be parallel to the bivector part
                //That last part is important because it means we can't do this in 5D since that no
                //longer always holds
                let [s, b1, b2, b3, b4, b5, b6, q] = self.cast_dim::<U4>().data;

                BiVec4::new(b1, b2, b3, b4, b5, b6).exp_even() *
                QuadVec4::new(q).exp_even_simple() *
                s.exp()

            }.cast_dim_generic(n),

            //any other evens don't have an easy closed-form pattern so we have to use
            //the taylor series
            _ => exp_selected(self, Even::one_generic(n), T::default_epsilon())

        }

    }

}

impl<T:RefRealField+AllocOdd<N>, N:Dim> Odd<T,N> {

    ///Computes the exponential of `self`
    pub fn exp(self) -> Multivector<T,N> where T:AllocMultivector<N> {
        let n = self.dim_generic();
        exp_selected(self, Multivector::one_generic(n), T::default_epsilon())
    }

}

impl<T:RefRealField+AllocMultivector<N>, N:Dim> Multivector<T,N> {

    ///Computes the exponential of `self`
    pub fn exp(self) -> Multivector<T,N> {

        //match the dimension so we can optimize for the first few dimensions
        let n = self.dim_generic();
        match n.value() {

            //a single scalar
            0 => {
                Self::from_iter_generic(n, self.into_iter().map(|x| x.exp()))
            },

            //split-complex numbers
            1 => {

                let [a, b] = self.cast_dim::<U1>().data;

                let (s,c) = b.sinh_cosh();
                Multivector1::new(c, s) * a.exp()

            }.cast_dim_generic(n),

            //any other evens don't have an easy closed-form pattern so we have to use
            //the taylor series
            _ => exp_selected(self, Multivector::one_generic(n), T::default_epsilon())

        }

    }

}


#[cfg(test)]
mod tests {

    use super::*;
    use rayon::prelude::*;
    use na::dimension::DimName;

    const EPSILON: f64 = 128.0*f64::EPSILON;

    //TODO: more tests for different values and grades

    #[test]
    fn simple_rot() {

        macro_rules! rot_test {
            ($n:ident) => {

                //this gets a little slow for high dimensions so we'll do this all in a parallelized loop
                (0..binom($n.value(),2)).into_par_iter().for_each(|i|

                    for a in -8..=8 {

                        let angle = (a as f64 * 45.0*10.0).to_radians();
                        // println!("{} {} {}", $n.value(), i, angle.to_degrees());

                        let b = BiVecN::basis_generic($n, U2::name(), i) * angle;

                        let mut rot = Multivector::zeroed_generic($n);
                        let start = rot.grade_index(2);
                        rot[0] = angle.cos();
                        rot[i+start] = angle.sin();

                        let rot_taylor = exp_selected(b.clone(), Multivector::one_generic($n), f64::EPSILON);
                        let rot_exp = b.clone().exp();

                        approx::assert_relative_eq!(rot, rot_taylor, max_relative=EPSILON, epsilon=EPSILON);
                        approx::assert_relative_eq!(rot, rot_exp, max_relative=EPSILON, epsilon=EPSILON);
                        approx::assert_relative_eq!(rot_taylor, rot_exp, max_relative=EPSILON, epsilon=EPSILON);


                        let mut rot_even = Even::zeroed_generic($n);
                        rot_even[0] = angle.cos();
                        rot_even[i+1] = angle.sin();

                        let rot_taylor_even = exp_selected(b.clone(), Even::one_generic($n), f64::EPSILON);
                        let rot_exp_even = b.exp_even();

                        approx::assert_relative_eq!(rot_even, rot_taylor_even, max_relative=EPSILON, epsilon=EPSILON);
                        approx::assert_relative_eq!(rot_even, rot_exp_even, max_relative=EPSILON, epsilon=EPSILON);
                        approx::assert_relative_eq!(rot_taylor_even, rot_exp_even, max_relative=EPSILON, epsilon=EPSILON);



                    }

                )
            }
        }

        //dynamic dims
        for n in 0..=7 {
            let n = Dynamic::new(n);
            rot_test!(n);
        }

        //static dims
        dim_name_test_loop!(
            @short |$N| {
                let n = $N::name();
                rot_test!(n);
            }
        );


    }

    #[test]
    fn double_rot_exp() {

        macro_rules! test {
            ($n:ident) => {{

                //a parallelized iterator for looping over a bunch of double angles
                let iter = {
                    (0..binom($n.value(),2)).into_par_iter()
                    .flat_map(|i| (0..=i).into_par_iter().map(move |j| (i,j)))
                    .flat_map(|(i,j)| (-3..3).into_par_iter().map(move |a| (i,j,a)))
                    .flat_map(|(i,j,a)| (-3..3).into_par_iter().map(move |b| (i,j,a,b)))
                };

                iter.for_each(
                    |(i,j,a,b)| {

                        let g = U2::name();

                        //two planes for two angles
                        let b1 = BiVecN::basis_generic($n,g,i) * (a as f64 * 120.0).to_radians();
                        let b2 = BiVecN::basis_generic($n,g,j) * (b as f64 * 120.0).to_radians();

                        //the angles combined
                        let b = &b1 + &b2;

                        let rot_taylor = exp_selected(b.clone(), Multivector::one_generic($n), f64::EPSILON);
                        let rot_exp = b.clone().exp();

                        let rot_taylor_even = exp_selected(b.clone(), Even::one_generic($n), f64::EPSILON);
                        let rot_exp_even = b.clone().exp_even();

                        let (rot, rot_even) = if (&b1^&b2).norm_sqrd() == 0.0 {
                            //if the two planes are not fully perpendicular
                            (b.clone().exp_simple(), b.clone().exp_even_simple())
                        } else {
                            //if they are completely orthogonal
                            (
                                b1.clone().exp_simple() * b2.clone().exp_simple(),
                                b1.exp_even_simple() * b2.exp_even_simple()
                            )
                        };

                        approx::assert_relative_eq!(rot, rot_taylor, max_relative=EPSILON, epsilon=EPSILON);
                        approx::assert_relative_eq!(rot, rot_exp, max_relative=EPSILON, epsilon=EPSILON);
                        approx::assert_relative_eq!(rot_taylor, rot_exp, max_relative=EPSILON, epsilon=EPSILON);

                        approx::assert_relative_eq!(rot_even, rot_taylor_even, max_relative=EPSILON, epsilon=EPSILON);
                        approx::assert_relative_eq!(rot_even, rot_exp_even, max_relative=EPSILON, epsilon=EPSILON);
                        approx::assert_relative_eq!(rot_taylor_even, rot_exp_even, max_relative=EPSILON, epsilon=EPSILON);
                    }
                )
            }};
        }

        //dynamic
        for n in 4..=6 {
            let n = Dynamic::new(n);
            test!(n)
        }

        //static
        dim_name_test_loop!(
            @short |$N| {
                let n = $N::name();
                test!(n);
            }
        );

    }


}


#[cfg(test)]
mod benches {

    use super::*;
    use test::black_box;
    use test::Bencher;

    #[bench]
    fn exp_4d_taylor(b: &mut Bencher) {
        b.iter(
            || black_box(
                exp_selected(black_box(BiVec4::new(1.0, 0.0, 0.0, 2.0, 0.0, 0.0)), Even4::one(), f64::EPSILON)
            )
        )
    }

    #[bench]
    fn exp_4d(b: &mut Bencher) {
        b.iter(
            || black_box(
                black_box(BiVec4::new(1.0, 0.0, 0.0, 2.0, 0.0, 0.0)).exp()
            )
        )
    }

    #[bench]
    fn exp_5d_taylor(b: &mut Bencher) {
        b.iter(
            || black_box(
                exp_selected(black_box(
                    BiVec5::new(1.0, 0.0, 0.0, 2.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0)
                ), Even5::one(), f64::EPSILON)
            )
        )
    }

    #[bench]
    fn exp_5d(b: &mut Bencher) {
        b.iter(
            || black_box(
                black_box(
                    BiVec5::new(1.0, 0.0, 0.0, 2.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0)
                ).exp()
            )
        )
    }

}
