
use super::*;

pub trait RefMul<Rhs:?Sized> {
    type Output;
    fn ref_mul<'a,'b>(&'a self, rhs:&'b Rhs) -> Self::Output;
}

impl<T1:?Sized,T2:?Sized,U> RefMul<T2> for T1 where for<'a,'b> &'a T1: Mul<&'b T2,Output=U> {
    type Output = U;
    fn ref_mul<'a,'b>(&'a self, rhs:&'b T2) -> U { self * rhs }
}

trait MultivectorSrc:IntoIterator {

    type Scalar;
    type Dim: Dim;

    fn dim(&self) -> Self::Dim;
    fn elements(&self) -> usize;

    fn get(&self, i:usize) -> &Self::Scalar;
    fn basis_blade(&self, i:usize) -> BasisBlade;
}

trait MultivectorDst: MultivectorSrc {

    type Shape: Copy;
    type Uninit: UninitStorage<Self::Scalar>;

    fn uninit(shape: Self::Shape) -> Self::Uninit;
    unsafe fn assume_init(uninit:Self::Uninit) -> Self;

    fn index_of(basis:BasisBlade, shape:Self::Shape) -> Option<(usize, bool)>;

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

impl<T:AllocBlade<N,G>, N:Dim, G:Dim> MultivectorDst for Blade<T,N,G> {

    type Shape = (N, G);
    type Uninit = <AllocateBlade<T,N,G> as Storage<T>>::Uninit;

    fn uninit((n,g): (N,G)) -> Self::Uninit {
        AllocateBlade::<T,N,G>::uninit(n,g)
    }

    unsafe fn assume_init(uninit: Self::Uninit) -> Self {
        Blade { data: uninit.assume_init() }
    }

    fn index_of(basis:BasisBlade, (n,g): (N,G)) -> Option<(usize, bool)> {
        if basis.grade() == g.value() {
            Some(basis.get_index_sign(n.value()))
        } else {
            None
        }
    }

}

unsafe fn _mul_selected<B1,B2,B3,N:Dim>(b1:B1, b2:B2, shape:B3::Shape) -> B3
where
    B1: MultivectorSrc<Dim=N>,
    B2: MultivectorSrc<Dim=N>,
    B3: MultivectorDst<Dim=N>,
    B1::Scalar: RefMul<B2::Scalar, Output=B3::Scalar>,
    B1::Item: Mul<B2::Item, Output=B3::Scalar>,
    B3::Scalar: ClosedAdd + ClosedSub + Neg<Output=B3::Scalar> + Zero,
{
    //To save further headache with generics, we don't allow multiplying two blades of
    //different dimension
    if b1.dim().value() != b2.dim().value() {
        panic!(
            "Cannot multiply two values of different dimensions: {}!={}",
            b1.dim().value(), b2.dim().value()
        )
    }

    //
    //The *slow* method
    //



    let mut dest = B3::uninit(shape);

    //if we can do the dot product
    //TODO: fix this to give the right sign
    // if b1.elements() == b2.elements() && dest.elements()==1 {
    //
    //     dest[0] = MaybeUninit::new(
    //         b1.into_iter().zip(b2).map(|(x1,x2)| x1*x2).fold(<B3::Scalar as Zero>::zero(), |c,x| c+x)
    //     );
    //
    //     return B3::assume_init(dest);
    //
    // }

    //TODO: fillin missing zeroes
    let mut written_to = vec![false; dest.elements()];

    //do the FOILiest of FOILs
    for i in 0..b1.elements() {
        let basis1 = b1.basis_blade(i);
        for j in 0..b2.elements() {
            let basis2 = b2.basis_blade(j);

            //mul the bases at i and j
            let basis3 = basis1 * basis2;

            //get the index and sign of the result
            if let Some((k, pos)) = B3::index_of(basis3, shape) {
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

    let res = B3::assume_init(dest);

    if b1.dim().value() != res.dim().value() {
        panic!(
            "Cannot multiply into value of different dimension: {}!={}",
            b1.dim().value(), res.dim().value()
        )
    } else {
        res
    }
}


impl<T1:AllocBlade<N,G1>, N:Dim, G1:Dim> Blade<T1,N,G1> {

    // pub fn mul_grade_generic<T2, U, G2:Dim, G:Dim>(self, rhs: Blade<T2,N,G2>, g: G) -> Blade<U,N,G>
    // where
    //     T1: RefMul<T2, Output=U>,
    //     T2: AllocBlade<N, G2>,
    //     U: AllocBlade<N, G> + Add<Output=U> + AddAssign + Sub<Output=U> + SubAssign + Neg<Output=U>,
    // {
    //     //TODO: fix when the
    //     unsafe { _mul_selected(self, rhs, g) }
    // }

}

impl<T1,T2,U,N:Dim,G1:Dim,G2:Dim> BitXor<Blade<T2,N,G2>> for Blade<T1,N,G1> where
    T1: AllocBlade<N,G1> + Mul<T2,Output=U> + RefMul<T2,Output=U>,
    T2: AllocBlade<N,G2>,
    G1: DimAdd<G2>,
    U: AllocBlade<N, DimSum<G1, G2>> + ClosedAdd + ClosedSub + Neg<Output=U> + Zero,
{
    type Output = Blade<U,N,DimSum<G1, G2>>;
    fn bitxor(self, rhs: Blade<T2,N,G2>) -> Self::Output {
        let (n, g) = (self.dim_generic(), self.grade_generic().add(rhs.grade_generic()));
        unsafe { _mul_selected(self, rhs, (n, g)) }
    }
}

impl<T1,T2,U,N:Dim,G1:Dim,G2:Dim> Rem<Blade<T2,N,G2>> for Blade<T1,N,G1> where
    T1: AllocBlade<N,G1> + Mul<T2,Output=U> + RefMul<T2,Output=U>,
    T2: AllocBlade<N,G2>,
    G2: DimSub<G1>,
    U: AllocBlade<N, DimDiff<G2, G1>> + ClosedAdd + ClosedSub + Neg<Output=U> + Zero,
{
    type Output = Blade<U,N,DimDiff<G2, G1>>;
    fn rem(self, rhs: Blade<T2,N,G2>) -> Self::Output {
        let (n, g) = (self.dim_generic(), rhs.grade_generic().sub(self.grade_generic()));
        unsafe { _mul_selected(self, rhs, (n, g)) }
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
