
use super::*;
use crate::subspace::Rotor;

//TODO: make work for Dynamic dims
#[inline(always)]
pub(crate) fn exp_selected<B1,B2,T:RefRealField,N:Dim>(x:B1, one:B2, epsilon: T::RealField) -> B2 where
    B1: MultivectorSrc<Scalar=T,Item=T,Dim=N>+Clone+DivAssign<T> + Debug,
    B2: MultivectorSrc<Scalar=T,Item=T,Dim=N>+MultivectorDst+Clone+AddAssign+DivAssign<T> + Debug,
    T: AllRefMul<T, AllOutput=T> + Debug,
{

    //for convenience
    let two = T::one() + T::one();
    let four = T::one() + T::one() + T::one() + T::one();

    //
    //First, we scale down x to have a norm less than one.
    //this is so that we can consistently get within epsilon using the remainder estimation theorem
    //

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

    let shape = one.shape();

    let mut exp = one.clone();
    let mut term = one;

    let mut i = T::one();
    let mut remainder = T::one();

    let eps = T::e() * epsilon * factor;

    //apply the taylor series for exp() until the remainder term is small enough
    while remainder > eps {

        //compute the next term `x^n / n!`
        term = mul_selected(term, x.clone(), shape);
        term /= i.clone();

        //add the term to the total
        exp += term.clone();

        //increment the index
        i += T::one();

        //update the upper bound for the remainder
        //note that this is
        remainder /= i.clone();

    }

    println!("{:?}", i);

    //finally, each of the halvings we did to the exponent translate back to squarings of the result
    for _ in 0..halvings {
        exp = mul_selected(exp.clone(), exp.clone(), shape);
    }

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

    (bivector, $self:ident, $mul:ident, $exp:ident) => {{
        //time for some fancy shit...

        //so in 4 and 5 dimensions, we can take the exponential by first decomposing the
        //bivector into two simple bivectors that are perpendicular and commute multiplicatively

        //I don't wanna explain how this works rn, so imma just say it's *m a g i c*

        let two = T::one() + T::one();

        let b = $self;
        let b_conj_scaled = (&b).mul_grade_generic((&b).$mul(&b).reverse(), b.grade_generic());

        let factor = (&b).$mul(&b_conj_scaled).into_iter().next().unwrap();
        let b_conj = b_conj_scaled / factor.sqrt();

        let b1 = (&b_conj + &b_conj) / &two;
        let b2 = (&b_conj - &b_conj) / &two;

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
            (n, 2) if n<6 => exp!(bivector, self, mul_full, exp_simple),

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
            (n, 2) if n<6 => exp!(bivector, self, mul_even, exp_even_simple),

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

            }.cast_dim_generic(n),

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

    const EPSILON: f64 = 128.0*f64::EPSILON;

    #[test]
    fn rot_2d() {

        for n in 1..3600 {

            let angle = BiVec2::new(100.0 * std::f64::consts::PI / n as f64);
            let rot: Even2<_> = exp_selected(angle, na::dimension::Const::<2>, EPSILON);

            approx::assert_relative_eq!(rot, Even2::new(angle.value.cos(), angle.value.sin()), max_relative=EPSILON, epsilon=EPSILON);

            println!("{}: exp({:+}) == {:+}", n, angle, rot);

        }


    }

    // #[test]
    // fn fun() {
    //
    //     let sqrt3 = 3.0f64.sqrt();
    //
    //     let rot = Even2::new(sqrt3, 1.0f64).normalize();
    //     let angle: Even2<_> = log_selected(rot, na::dimension::Const::<2>, EPSILON);
    //
    //     println!("log({:+}) == {:+}", rot, angle);
    //     println!("{}\n", angle[1]*6.0);
    //
    //     let rot = Even3::new(sqrt3, 1.0/sqrt3, -1.0/sqrt3, 1.0f64/sqrt3).normalize();
    //     let angle: Even3<_> = log_selected(rot, na::dimension::Const::<3>, EPSILON);
    //
    //     println!("log({:+}) == {:+}", rot, angle);
    //     println!("{}\n", angle[2]*6.0*3.0.sqrt());
    //
    //     let alpha = 1.0f64;
    //     let rot1 = Even4::new(1.0, 1.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0).normalize();
    //     let rot2 = Even4::new(1.0, 0.0, 0.0, 0.0, 1.0, 0.0, 0.0, 0.0).normalize();
    //     let rot3 = Even4::new(0.5, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, -0.5);
    //     let rot4 = rot1 * rot2 * rot3;
    //     // let angle3: Even4<_> = log_selected(rot3, na::dimension::Const::<4>, EPSILON);
    //
    //     println!("{}\n{}\n{}\n{}\n{}", rot1, rot2, rot1*rot2, rot3, rot4);
    //
    //     // println!("log({:+}) == {:+}", rot1, angle1);
    //     // println!("log({:+}) == {:+}", rot2, angle2);
    //     // println!("log({:+}) == {:+}", rot3, angle3);
    //     // println!("{}", angle[7]);
    //
    //     // let rot1 = Even4::new(1.0, 2.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0f64).normalize();
    //     // let rot2 = Even4::new(2.0, 0.0, 0.0, 0.0, 1.0, 0.0, 0.0, 0.0f64).normalize();
    //     // let rot = rot1*rot2;
    //     // let angle: Even4<_> = log_selected(rot, na::dimension::Const::<4>, EPSILON);
    //     //
    //     // println!("log({:+}) == {:+}", rot, angle);
    //     // println!("{} {}", angle[1]*2.0, angle[4]*2.0);
    //
    // }

}
