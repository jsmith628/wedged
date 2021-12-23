
use super::*;

//TODO: make work for Dynamic dims
pub(crate) fn exp_selected<B1,B2,T:ComplexField,N:Dim>(x:B1, shape: B2::Shape, epsilon: T::RealField) -> B2 where
    B1: MultivectorSrc<Scalar=T,Item=T,Dim=N>+Clone+DivAssign<T> + Debug,
    B2: MultivectorSrc<Scalar=T,Item=T,Dim=N>+MultivectorDst+Clone+AddAssign+DivAssign<T>+One + Debug,
    T: AllRefMul<T, AllOutput=T> + Debug,
{

    //for convenience
    let c2 = T::one() + T::one();
    let c4 = T::one() + T::one() + T::one() + T::one();
    let r2 = c2.clone().real();
    let r4 = c4.clone().real();

    //
    //First, we scale down x to have a norm less than one.
    //this is so that we can consistently get within epsilon using the remainder estimation theorem
    //

    let mut halvings = 0;
    let mut x = x;
    let mut norm_sqrd = (0..x.elements()).map(|i| x.get(i).modulus_squared() ).fold(T::zero().real(), |n,t| n+t);
    let mut factor = T::one().real();

    //divide the multivector by 2 until the norm is less than one
    while norm_sqrd > T::one().real() {
        factor /= r2.clone();
        x /= c2.clone();
        norm_sqrd /= r4.clone();
        halvings += 1;
    }

    let mut exp = B2::one();
    let mut term = B2::one();

    let mut i = T::one();
    let mut remainder = T::one().real();

    //apply the taylor series for exp() until the remainder term is small enough
    while remainder > epsilon * factor {

        term = mul_selected(term, x.clone(), shape);
        term /= i.clone();
        remainder /= i.clone().real() + T::one().real();

        exp += term.clone();
        i += T::one();

    }

    println!("{:?}", i);

    //finally, each of the halvings we did to the exponent translate back to squarings of the result
    for _ in 0..halvings {
        exp = mul_selected(exp.clone(), exp.clone(), shape);
    }

    exp

}

impl<T:RefComplexField+AllocBlade<N,G>+AllocEven<N>, N:DimName, G:Dim> Blade<T,N,G> {

    pub fn exp_even(mut self) -> Even<T,N> {

        //match the dimension so we can optimize for the first few dimensions
        let (n, g) = self.shape();

        if n.value()==0 {
            //a single scalar just gets exp normally
            self[0] = self[0].exp();
            Even::from_blade(self)
        } else {

            let guarranteed_simple = g.value()==1 || g.value()+1 >= n.value();
            if guarranteed_simple {

                //if we have a scalar, vector, psuedovector, or psuedoscalar, we
                //can easily take the exponential.
                //To do this, we treat the blade as `norm*b` since b is simple, `b*b == 1 or -1`
                //meaning that `exp(norm*b) == cos(norm) + sin(norm)*b` or
                //`exp(norm*b) == cosh(norm) + sinh(norm)*b` depending on the signature of b

                let (even, neg) = (self.even(), self.neg_sig());
                let (norm, b) = self.norm_and_normalize();

                //if the norm is zero, we have to have this base case to avoid NaNs in b
                if norm.is_zero() { return Even::one(); }

                match (even, neg) {
                    (true, true) => {
                        let mut exp = Even::from(b * norm.sin());
                        exp[0] = norm.cos();
                        exp
                    },
                    (true, false) => {
                        let mut exp = Even::from(b * norm.sinh());
                        exp[0] = norm.cosh();
                        exp
                    },
                    (false, true) => {
                        let mut exp = Even::zeroed_generic(n);
                        exp[0] = norm.cos();
                        exp
                    },
                    (false, false) => {
                        let mut exp = Even::zeroed_generic(n);
                        exp[0] = norm.cosh();
                        exp
                    }
                }

            }
            else if n.value()<6 && g.value()==2 {

                //time for some fancy shit...

                //so in 4 and 5 dimensions, we can take the exponential by first decomposing the
                //bivector into two simple bivectors that are perpendicular and commute multiplicatively

                //I don't wanna explain how this works rn, so imma just say it's *m a g i c*

                let two = T::one() + T::one();

                let b = self;
                let b_conj_scaled = (&b).mul_grade_generic((&b).mul_even(&b).reverse(), g);

                let factor = (&b).mul_even(&b_conj_scaled)[0];
                let b_conj = b_conj_scaled / factor.sqrt();

                let b1 = (&b_conj + &b_conj) / &two;
                let b2 = (&b_conj - &b_conj) / &two;

                let (norm1, b1) = b1.norm_and_normalize();
                let (norm2, b2) = b2.norm_and_normalize();

                let mut exp1 = Even::from_blade(b1*norm1.sin());
                exp1[0] = norm1.cos();
                let mut exp2 = Even::from_blade(b2*norm2.sin());
                exp2[0] = norm2.cos();

                exp1 * exp2

            }
            else {

                //if not simple, we gotta use the taylor series
                exp_selected(self, n, <T::RealField as AbsDiffEq>::default_epsilon())
            }

        }

    }

}

//TODO: make work for Dynamic dims
impl<T:RefComplexField+AllocEven<N>, N:DimName> Even<T,N> {

    pub fn exp(self) -> Even<T,N> {

        //match the dimension so we can optimize for the first few dimensions
        let n = self.dim_generic();
        match n.value() {

            //a single scalar
            0 | 1 => Even::from_element_generic(n, self[0].exp()),

            _ => exp_selected(self, n, <T::RealField as AbsDiffEq>::default_epsilon())

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
