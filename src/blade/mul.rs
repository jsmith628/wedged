
use super::*;
use crate::basis_blade::BasisBlade;

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

impl<T:Alloc<N,G>, N:Dim, G:Dim> MultivectorSrc for Blade<T,N,G> {
    type Scalar = T;
    type Dim = N;

    fn dim(&self) -> N { self.dim_generic() }
    fn elements(&self) -> usize { Blade::elements(self) }
    fn get(&self, i:usize) -> &T { &self[i] }
    fn basis_blade(&self, i:usize) -> BasisBlade {
        BasisBlade::basis_blade(Blade::dim(self), self.grade(), i)
    }

}

impl<'a, T:Alloc<N,G>, N:Dim, G:Dim> MultivectorSrc for &'a Blade<T,N,G> {

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
    U: Alloc<N, G> + Add<Output=U> + AddAssign + Sub<Output=U> + SubAssign + Neg<Output=U>,
{
    //To save further headache with generics, we don't allow multiplying two blades of
    //different dimension
    if b1.dim().value() != b2.dim().value() {
        panic!(
            "Cannot multiply two blades of different dimensions: {}!={}",
            b1.dim().value(), b2.dim().value()
        )
    }

    //for convenience
    let n = b1.dim();

    //
    //The *slow* method
    //

    let mut dest = Allocate::<U,N,G>::uninit(b1.dim(), g);
    let mut written_to = vec![false; dest.elements()];

    //do the FOILiest of FOILs
    for i in 0..b1.elements() {
        let basis1 = b1.basis_blade(i);
        for j in 0..b2.elements() {
            let basis2 = b1.basis_blade(j);

            //mul the bases at i and j
            let basis3 = basis1 * basis2;

            //if the result is at the selected grade
            if basis3.grade() == g.value() {
                //get the index and sign of the result
                let (k, neg) = basis3.get_index_sign(n.value());

                //multiply the two terms
                let term = b1.get(i).ref_mul(b2.get(j));
                let term = if neg { -term } else { term };

                //write or add the result to the destination blade
                if written_to[k] {
                    //TODO: change once assume_init_ref() is stable
                    if neg {
                        *dest[k].as_mut_ptr() -= term;
                    } else {
                        *dest[k].as_mut_ptr() += term;
                    }
                } else {
                    dest[k] = MaybeUninit::new(if neg {-term} else {term});
                    written_to[k] = true;
                }

            }


        }
    }

    Blade { data: dest.assume_init() }
}


impl<T1:Alloc<N,G1>, N:Dim, G1:Dim> Blade<T1,N,G1> {

    pub fn mul_grade_generic<T2, U, G2:Dim, G:Dim>(self, rhs: Blade<T2,N,G2>, g: G) -> Blade<U,N,G>
    where
        T1: RefMul<T2, Output=U>,
        T2: Alloc<N, G2> + Clone,
        U: Alloc<N, G> + Add<Output=U> + AddAssign + Sub<Output=U> + SubAssign + Neg<Output=U>,
    {
        unsafe { _mul_grade(self, rhs, g) }
    }

}
