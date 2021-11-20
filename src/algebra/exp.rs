
use super::*;

pub(crate) fn exp_selected<B1,B2,T:RealField,N:Dim>(x:B1, shape: B2::Shape, epsilon:T) -> B2 where
    B1: MultivectorSrc<Scalar=T,Item=T,Dim=N>+Clone+DivAssign<T> + Debug,
    B2: MultivectorSrc<Scalar=T,Item=T,Dim=N>+MultivectorDst+Clone+AddAssign+DivAssign<T>+One + Debug,
    T: RefMul<T, Output=T> + Debug,
{

    //
    //First, we scale down x to have a norm less than one.
    //this is so that wed can consistently get within epsilon using the remainder estimation theorem
    //

    //
    //Ok, so I know this is pretty spicy, but we can prove this works with the following:
    //
    //- First, consider our expression `1 + 1 + 1 + 1`
    //- Next, using `Succ(x)` as the Peano successor function, we can define `1` as `Succ(0)`,
    //  reducing the above to `Succ(0) + Succ(0) + Succ(0) + Succ(0)`
    //- Next, by convention, repeated applications of the `+` operator can be reduced to a sequence
    //  of binary operations by adding parentheses: `(((Succ(0) + Succ(0)) + Succ(0)) + Succ(0))`
    //- Then, note that by definition of the `+` operator, we have `Succ(x) + Succ(y) == Succ(Succ(x)) + y`
    //  so we can reduce to `(((Succ(Succ(0)) + 0) + Succ(0)) + Succ(0))`
    //- Additionally, using another axiom of `+`, we have `x + 0 = x`, reducing further to:
    //  `((Succ(Succ(0)) + Succ(0)) + Succ(0))`
    //- Next, we can simply apply these rules furthermore in succession as follows:
    //  `((Succ(Succ(0)) + Succ(0)) + Succ(0))`
    //  `((Succ(Succ(Succ(0))) + 0) + Succ(0))`
    //  `(Succ(Succ(Succ(0))) + Succ(0))`
    //  `(Succ(Succ(Succ(Succ(0)))) + 0)`
    //  `Succ(Succ(Succ(Succ(0))))`
    //- However, this final expression happens to coincide with the definition of the propositional
    //  symbol `four`
    //
    //Therefore, `1 + 1 + 1 + 1` equals `four`
    //
    let two = T::one() + T::one();
    let four = T::one() + T::one() + T::one() + T::one();


    let mut doublings = 0;
    let mut x = x;
    let mut norm_sqrd = (0..x.elements()).map(|i| x.get(i).ref_mul(x.get(i)) ).fold(T::zero(), |n,t| n+t);
    let mut factor = T::one();

    while norm_sqrd > T::one() {

        // println!("{} {} {}")

        factor /= two.clone();
        x /= two.clone();
        norm_sqrd /= four.clone();
        doublings += 1;
    }

    let mut exp = B2::one();
    let mut term = B2::one();

    let mut i = T::one();
    let mut remainder = T::one();

    //TODO: figure out what the RHS here should actually be
    while remainder > epsilon * factor {

        term = mul_selected(term, x.clone(), shape);
        term /= i.clone();
        remainder /= i.clone() + T::one();

        exp += term.clone();
        i += T::one();

    }

    for _ in 0..doublings {
        exp = mul_selected(exp.clone(), exp.clone(), shape);
    }

    exp

}

pub(crate) fn log_selected<B1,B2,T:RealField,N:Dim>(x:B1, shape: B2::Shape, epsilon:T) -> B2 where
    B1: MultivectorSrc<Scalar=T,Item=T,Dim=N>+Clone+DivAssign<T>+SubAssign + Display +One,
    B2: MultivectorSrc<Scalar=T,Item=T,Dim=N>+MultivectorDst+Div<T,Output=B2>+Mul<T,Output=B2>+Clone+SubAssign+AddAssign+MulAssign<T>+DivAssign<T>+One+Zero + Display,
    T: RefMul<T, Output=T> + Debug,
{

    let two = T::one() + T::one();

    //first, normalize to have a better chance of getting within the ball of convergence
    let mut factor = T::one();
    let mut x = x;
    println!("{:+}", x);

    let norm = (0..x.elements()).map(|i| x.get(i).ref_mul(x.get(i)) ).fold(T::zero(), |n,t| n+t).sqrt();
    x /= norm;

    //Here, we use the babylonian method to take repeated square roots of x
    // let doublings = 40;
    // let mut roots_x:B2 = mul_selected(B2::one(), x.clone(), shape);
    // for _ in 0..doublings {
    //
    //     println!("{:+}", roots_x);
    //     let mut x_k = B2::one();
    //     for _ in 0..15 {
    //
    //         let mut x_k_inv = x_k.clone();
    //         let n = (0..x_k_inv.elements()).map(|i| x_k_inv.get(i).ref_mul(x_k_inv.get(i)) ).fold(T::zero(), |n,t| n+t);
    //         for i in 0..x_k_inv.elements() {
    //             if x_k_inv.basis(i).grade() & 0b10 != 0 {
    //                 x_k_inv.set(i, -x_k_inv.get(i).clone())
    //             }
    //         }
    //         x_k_inv /= n;
    //
    //         x_k += mul_selected(roots_x.clone(), x_k_inv, shape);
    //         x_k /= two;
    //     }
    //
    //     roots_x = x_k
    //
    // }

    // println!("{:+}", roots_x);

    // let mut x = roots_x;

    //next subtract 1 since the series is around x=1
    x -= B1::one();

    //get the norm so we can estimate the remainder
    let norm_x_1 = (0..x.elements()).map(|i| x.get(i).ref_mul(x.get(i)) ).fold(T::zero(), |n,t| n+t).sqrt();


    println!("{:+}", x);

    //Then, we compute using the taylor series of ln

    let mut log = B2::zero();
    let mut x_n = B2::one();

    let mut i = T::one();
    let mut sign = T::one();

    let mut remainder = T::one();

    while remainder.clone() / i.abs() > epsilon {

        x_n = mul_selected(x_n, x.clone(), shape);
        let term = x_n.clone() * sign / i.clone();

        println!("{:?}: [{:+}] [{:+}]", i, term, log);

        log += term;

        i += T::one();
        remainder *= norm_x_1.clone();

        sign = -sign;

    }

    // let mut log = x;
    // for _ in 0..doublings {
    //     log *= two.clone();
    // }

    //finally, add back in the log of the factors we divided by
    log += B2::one() * norm.ln();
    println!("[{:+}]", log);

    log

}

#[cfg(test)]
mod tests {

    use super::*;

    const EPSILON: f64 = 0.00000000000001;

    #[test]
    fn rot_2d() {

        for n in 1..3600 {

            let angle = BiVec2::new(10.0 * std::f64::consts::PI / n as f64);
            let rot: Even2<_> = exp_selected(angle, na::dimension::Const::<2>, EPSILON);

            approx::assert_relative_eq!(rot, Even2::new(angle.value.cos(), angle.value.sin()), epsilon=EPSILON);

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
