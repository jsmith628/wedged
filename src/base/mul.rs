
use super::*;

pub trait RefMul<Rhs:?Sized> {
    type Output;
    fn ref_mul<'a,'b>(&'a self, rhs:&'b Rhs) -> Self::Output;
}

impl<T1:?Sized,T2:?Sized,U> RefMul<T2> for T1 where for<'a,'b> &'a T1: Mul<&'b T2,Output=U> {
    type Output = U;
    fn ref_mul<'a,'b>(&'a self, rhs:&'b T2) -> U { self * rhs }
}

trait MultivectorSrc {

    type Scalar;
    type Dim: Dim;

    fn dim(&self) -> Self::Dim;
    fn elements(&self) -> usize;

    fn get(&self, i:usize) -> &Self::Scalar;
    fn basis_blade(&self, i:usize) -> BasisBlade;
}

impl<T:AllocBlade<N,G>, N:Dim, G:Dim> MultivectorSrc for Blade<T,N,G> {

    type Scalar = T;
    type Dim = N;

    fn dim(&self) -> N { self.dim_generic() }
    fn elements(&self) -> usize { Blade::elements(self) }
    fn get(&self, i:usize) -> &T { &self[i] }
    fn basis_blade(&self, i:usize) -> BasisBlade {
        BasisBlade::basis_blade(Blade::dim(self), self.grade(), i)
    }

}

impl<'a, T:AllocBlade<N,G>, N:Dim, G:Dim> MultivectorSrc for &'a Blade<T,N,G> {

    type Scalar = T;
    type Dim = N;

    fn dim(&self) -> N { self.dim_generic() }
    fn elements(&self) -> usize { Blade::elements(self) }

    fn get(&self, i:usize) -> &T { &self[i] }
    fn basis_blade(&self, i:usize) -> BasisBlade {
        BasisBlade::basis_blade(Blade::dim(self), self.grade(), i)
    }

}

unsafe fn _mul_grade<B1,B2,U,N:Dim,G:Dim>(b1:B1, b2:B2, g:G) -> Blade<U,N,G>
where
    B1: MultivectorSrc<Dim=N>,
    B2: MultivectorSrc<Dim=N>,
    B1::Scalar: RefMul<B2::Scalar, Output=U>,
    U: AllocBlade<N, G> + Add<Output=U> + AddAssign + Sub<Output=U> + SubAssign + Neg<Output=U>,
{
    //To save further headache with generics, we don't allow multiplying two blades of
    //different dimension
    if b1.dim().value() != b2.dim().value() {
        panic!(
            "Cannot multiply two values of different dimensions: {}!={}",
            b1.dim().value(), b2.dim().value()
        )
    }

    //for convenience
    let n = b1.dim();

    //
    //The *slow* method
    //

    let mut dest = AllocateBlade::<U,N,G>::uninit(b1.dim(), g);
    let mut written_to = vec![false; dest.elements()];

    //do the FOILiest of FOILs
    for i in 0..b1.elements() {
        let basis1 = b1.basis_blade(i);
        for j in 0..b2.elements() {
            let basis2 = b2.basis_blade(j);

            //mul the bases at i and j
            let basis3 = basis1 * basis2;

            //if the result is at the selected grade
            if basis3.grade() == g.value() {
                //get the index and sign of the result
                let (k, pos) = basis3.get_index_sign(n.value());

                //multiply the two terms
                let term = b1.get(i).ref_mul(b2.get(j));

                //write or add the result to the destination blade
                if written_to[k] {
                    //TODO: change once assume_init_ref() is stable
                    if pos {
                        *dest[k].as_mut_ptr() += term;
                    } else {
                        *dest[k].as_mut_ptr() -= term;
                    }
                } else {
                    dest[k] = MaybeUninit::new(if pos {term} else {-term});
                    written_to[k] = true;
                }

            }


        }
    }

    Blade { data: dest.assume_init() }
}


impl<T1:AllocBlade<N,G1>, N:Dim, G1:Dim> Blade<T1,N,G1> {

    // pub fn mul_grade_generic<T2, U, G2:Dim, G:Dim>(self, rhs: Blade<T2,N,G2>, g: G) -> Blade<U,N,G>
    // where
    //     T1: RefMul<T2, Output=U>,
    //     T2: AllocBlade<N, G2>,
    //     U: AllocBlade<N, G> + Add<Output=U> + AddAssign + Sub<Output=U> + SubAssign + Neg<Output=U>,
    // {
    //     //TODO: fix when the
    //     unsafe { _mul_grade(self, rhs, g) }
    // }

}

impl<T1,T2,U,N:Dim,G1:Dim,G2:Dim> BitXor<Blade<T2,N,G2>> for Blade<T1,N,G1> where
    T1: AllocBlade<N,G1> + RefMul<T2,Output=U>,
    T2: AllocBlade<N,G2>,
    G1: DimAdd<G2>,
    U: AllocBlade<N, DimSum<G1, G2>> + Add<Output=U> + AddAssign + Sub<Output=U> + SubAssign + Neg<Output=U>,
{
    type Output = Blade<U,N,DimSum<G1, G2>>;
    fn bitxor(self, rhs: Blade<T2,N,G2>) -> Self::Output {
        let g = self.grade_generic().add(rhs.grade_generic());
        unsafe { _mul_grade(self, rhs, g) }
    }
}

impl<T1,T2,U,N:Dim,G1:Dim,G2:Dim> Rem<Blade<T2,N,G2>> for Blade<T1,N,G1> where
    T1: AllocBlade<N,G1> + RefMul<T2,Output=U>,
    T2: AllocBlade<N,G2>,
    G2: DimSub<G1>,
    U: AllocBlade<N, DimDiff<G2, G1>> + Add<Output=U> + AddAssign + Sub<Output=U> + SubAssign + Neg<Output=U>,
{
    type Output = Blade<U,N,DimDiff<G2, G1>>;
    fn rem(self, rhs: Blade<T2,N,G2>) -> Self::Output {
        let g = rhs.grade_generic().sub(self.grade_generic());
        unsafe { _mul_grade(self, rhs, g) }
    }
}

#[cfg(test)]
mod tests {

    use super::*;

    macro_rules! test_mul {
        ($b1:ident $op:tt $b2:ident == $b3:expr; $commutative:literal) => {

            assert_eq!( $b1 $op $b2,  $b3);
            assert_eq!(-$b1 $op $b2, -$b3);
            assert_eq!( $b1 $op-$b2, -$b3);
            assert_eq!(-$b1 $op-$b2,  $b3);

            if $commutative {
                assert_eq!( $b2 $op $b1,  $b3);
                assert_eq!(-$b2 $op $b1, -$b3);
                assert_eq!( $b2 $op-$b1, -$b3);
                assert_eq!(-$b2 $op-$b1,  $b3);
            } else {
                assert_eq!( $b2 $op $b1, -$b3);
                assert_eq!(-$b2 $op $b1,  $b3);
                assert_eq!( $b2 $op-$b1,  $b3);
                assert_eq!(-$b2 $op-$b1, -$b3);
            }

        }
    }

    #[test]
    fn basis() {

        let e = Scalar3::new(1);

        let e1 = Vec3::new(1, 0, 0);
        let e2 = Vec3::new(0, 1, 0);
        let e3 = Vec3::new(0, 0, 1);

        let e23 = BiVec3::new(1, 0, 0);
        let e31 = BiVec3::new(0, 1, 0);
        let e12 = BiVec3::new(0, 0, 1);

        let e123 = TriVec3::new(1);

        let zero = Scalar3::new(0);
        let zerov = Vec3::zero();
        let zerob = BiVec3::zero();
        let zeroq = Blade::<_,U3,U4>::zero();

        test_mul!(e^e == e; true);
        test_mul!(e^e1 == e1; true);
        test_mul!(e^e2 == e2; true);
        test_mul!(e^e3 == e3; true);
        test_mul!(e^e23 == e23; true);
        test_mul!(e^e31 == e31; true);
        test_mul!(e^e23 == e23; true);
        test_mul!(e^e123 == e123; true);

        test_mul!(e1^e1 == zerob; false);
        test_mul!(e2^e2 == zerob; false);
        test_mul!(e3^e3 == zerob; false);

        test_mul!(e23^e23 == zeroq; false);
        test_mul!(e31^e31 == zeroq; false);
        test_mul!(e12^e12 == zeroq; false);

        test_mul!(e1^e2 == e12; false);
        test_mul!(e3^e1 == e31; false);
        test_mul!(e2^e3 == e23; false);

        test_mul!(e1^e23 == e123; true);
        test_mul!(e2^e31 == e123; true);
        test_mul!(e3^e12 == e123; true);

        assert_eq!(e%e, e);
        assert_eq!(e%e1, e1);
        assert_eq!(e%e2, e2);
        assert_eq!(e%e3, e3);
        assert_eq!(e%e23, e23);
        assert_eq!(e%e31, e31);
        assert_eq!(e%e12, e12);
        assert_eq!(e%e123, e123);

        test_mul!(e1%e1 == e; true);
        test_mul!(e1%e2 == zero; true);
        test_mul!(e1%e3 == zero; true);
        test_mul!(e2%e2 == e; true);
        test_mul!(e2%e3 == zero; true);
        test_mul!(e3%e3 == e; true);

        assert_eq!(e1%e23, zerov);
        assert_eq!(e1%e31, -e3);
        assert_eq!(e1%e12, e2);
        assert_eq!(e2%e23, e3);
        assert_eq!(e2%e31, zerov);
        assert_eq!(e2%e12, -e1);
        assert_eq!(e3%e23, -e2);
        assert_eq!(e3%e31, e1);
        assert_eq!(e3%e12, zerov);

        assert_eq!(e1%e123, e23);
        assert_eq!(e2%e123, e31);
        assert_eq!(e3%e123, e12);
        assert_eq!(e23%e123, -e1);
        assert_eq!(e31%e123, -e2);
        assert_eq!(e12%e123, -e3);

    }

}
