
use super::*;
use crate::subspace::Rotor;

#[inline(always)]
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

    (bivector, $self:ident, $M:ident, $mul:ident, $exp:ident) => {{
        //time for some fancy shit...

        //so in 4 and 5 dimensions, we can take the exponential by first decomposing the
        //bivector into two simple bivectors that are perpendicular and commute multiplicatively

        //I don't wanna explain how this works rn, so imma just say it's *m a g i c*

        let n = $self.dim_generic();
        let two = T::one() + T::one();

        let b = $self;
        let mut b_sqrd = (&b).$mul(&b);

        let start = b_sqrd.grade_index(4);
        let bin4 = binom(n.value(), 4);
        for i in start..(start+bin4) {
            b_sqrd[i] = b_sqrd[i].ref_neg();
        }

        let b_conj_scaled = (&b).mul_grade_generic(&b_sqrd, b.grade_generic());

        let factor = (&b).$mul(&b_conj_scaled).into_iter().next().unwrap();

        //edge case that happens when both rotation planes have the same angle
        if factor.is_zero() {

            //TODO: this can probably be optimized pretty heavily

            //first, we reuse the squared b from earlier
            let mut exp = b_sqrd;

            //get the angle by normalizing
            //we can optimize a little by reusing the scalar part of `exp` for the square norm
            let angle_sqrd = exp[0].clone();

            if angle_sqrd.is_zero() { return $M::one_generic(n); }

            //(the two is to adjust for the fact that there are two rotation planes)
            //also, it's negative since 2blades square negative
            let angle = angle_sqrd.ref_div(&two.ref_neg()).sqrt();
            let b_hat = b / &angle;

            let (s, c) = angle.clone().sin_cos();

            //This also could probably be waaaay better

            //scalar part
            exp[0] = c.ref_mul(&c);

            //bivec part
            let start = exp.grade_index(2);
            let bin2 = binom(n.value(), 2);
            for i in 0..bin2 {
                exp[i+start] = b_hat[i].ref_mul(&s) * &c;
            }

            //quadvec part
            let start = exp.grade_index(4);
            for i in 0..bin4 {
                //we have to both cancel a negative from above and a factor of two
                //both of which are automatically in angle_sqrd6
                exp[i+start] *= s.ref_mul(&s) / &angle_sqrd;
            }

            return exp;
        }

        let b_conj = b_conj_scaled / factor.sqrt();

        let b1 = (&b + &b_conj) / &two;
        let b2 = (&b - &b_conj) / &two;

        b1.$exp() * b2.$exp()
    }}
}

impl<T:RefRealField+AllocBlade<N,U2>, N:Dim> BiVecN<T,N> {

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

    pub fn exp(self) -> Multivector<T,N> where T:AllocMultivector<N> {

        //match the dimension so we can optimize for the first few dimensions
        let (n, g) = self.shape();

        match (n.value(), g.value()) {
            //scalars do scalar things
            (_, 0) => exp!(scalar, self, Multivector),

            //if we're guaranteed to be simple
            (n, g) if g==1 || g+1>=n => self.exp_simple(),

            //*magic*
            (n, 2) if n<6 => exp!(bivector, self, Multivector, mul_full, exp_simple),

            //if not simple, we gotta use the taylor series
            _ => exp_selected(self, Multivector::one_generic(n), T::default_epsilon())
        }

    }

    pub fn exp_even(self) -> Even<T,N> where T:AllocEven<N> {

        //match the dimension so we can optimize for the first few dimensions
        let (n, g) = self.shape();

        match (n.value(), g.value()) {
            //scalars do scalar things
            (_, 0) => exp!(scalar, self, Even),

            //if we're guaranteed to be simple
            (n, g) if g==1 || g+1>=n => self.exp_even_simple(),

            //*magic*
            (n, 2) if n<6 => exp!(bivector, self, Even, mul_even, exp_even_simple),

            //if not simple, we gotta use the taylor series
            _ => exp_selected(self, Even::one_generic(n), T::default_epsilon())
        }

    }

}

//TODO: make work for Dynamic dims
impl<T:RefRealField+AllocEven<N>, N:Dim> Even<T,N> {

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

    pub fn exp(self) -> Multivector<T,N> where T:AllocMultivector<N> {
        let n = self.dim_generic();
        exp_selected(self, Multivector::one_generic(n), T::default_epsilon())
    }

}

impl<T:RefRealField+AllocMultivector<N>, N:Dim> Multivector<T,N> {

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
                    .flat_map(|i| (0..binom($n.value(),2)).into_par_iter().map(move |j| (i,j)))
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
    fn exp_taylor_4d(b: &mut Bencher) {
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

}
