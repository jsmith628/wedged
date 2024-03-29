
use super::*;

impl<T:AllocBlade<N,G>, N:Dim, G:Dim> Blade<T,N,G> where
    T:AllocBlade<N,DimDiff<N,G>>+Neg<Output=T>,
    N: DimSub<G>
{

    ///
    /// Computes the dual of this element in the current dimension
    ///
    /// This produces a blade representing the subspace(s) containing all vectors perpendicular
    /// to `self`. For example, the dual of a vector will give a psuedovector representing a
    /// hyperplane with the vector as its normal, and the dual of the psuedovector of a hyperplane
    /// will give its vector normal.
    ///
    /// This computation is equivalent to `self / I` where `I` is the psuedoscalar of the space,
    /// but due to symmetries in how the basis blades are [chosen](BasisBlade::basis_blade),
    /// this _usually_ is done with just a simple copy or negation of the components.
    ///
    /// In fact, the bases are chosen **specifically** so that the components of a psuedovector
    /// are exactly the same as the components of its dual/normal. Though, the converse is not
    /// always true
    ///
    /// # Examples
    /// ```
    /// # use wedged::algebra::*;
    ///
    /// //In 3D, a bivector represents a plane, and its dual is its normal
    /// let plane = BiVec3::new(6, 2, 8);
    /// let n = plane.dual();
    ///
    /// assert_eq!(n.as_slice(), plane.as_slice());
    ///
    /// //Likewise, in 4D, a trivector represents a hyperplane, and its dual is its normal
    /// let hyperplane = TriVec4::new(6, 2, 8, 3);
    /// let n = hyperplane.dual();
    ///
    /// assert_eq!(n.as_slice(), hyperplane.as_slice());
    ///
    /// ```
    ///
    pub fn dual(self) -> DualBlade<T,N,G> {

        if self.dim() < self.grade() {
            panic!(
                "Cannot take the dual of a blade with grade greater than dim: {}>{}",
                self.dim(), self.grade()
            );
        }

        //there is unfortunately not much we can do to avoid this
        let (n, g) = (self.dim_generic(), self.grade_generic());
        let mut dst = AllocateBlade::<T,N,DimDiff<N,G>>::uninit(n, n.sub(g));

        //for convenience
        let (n, g, e) = (self.dim(), self.grade(), self.elements());
        let mut b = self.into_iter();

        //if the inverse of the psuedoscalar negates the psuedoscalar
        let neg = n & 0b10 != 0;

        if 2*g < n && neg {
            for i in 0..e { dst[i] = MaybeUninit::new(-b.next().unwrap()) }
        } else if 2*g == n && n!=0 {

            //for grades at the exact middle of a dimension, half gets negated, half gets copied

            //negate the bottom half, copy the top half
            if neg {
                for i in 0..e/2 { dst[e/2 + i] = MaybeUninit::new(-b.next().unwrap()) }
            } else {
                for i in 0..e/2 { dst[e/2 + i] = MaybeUninit::new(b.next().unwrap()) }
            }
            for i in 0..e/2 { dst[i] = MaybeUninit::new(b.next().unwrap()) }

        } else {
            for i in 0..e { dst[i] = MaybeUninit::new(b.next().unwrap()) }
        }

        Blade { data: unsafe { dst.assume_init() } }

    }

    ///
    /// Computes the element whose dual is this value
    ///
    /// This is essentially just the [dual](Blade::dual()), but negated in certain dimensions.
    ///
    /// Specifially, whereas the _dual_ is found by `self / I`, the _undual_ is found by
    /// `self * I`. So in dimensions where `I⁻¹ == I`, the undual is the same as the dual, and in
    /// dimensions where `I⁻¹ == -I`, it is the negative of the dual.
    ///
    pub fn undual(self) -> DualBlade<T,N,G> {

        if self.dim() < self.grade() {
            panic!(
                "Cannot take the dual of a blade with grade greater than dim: {}>{}",
                self.dim(), self.grade()
            );
        }

        //there is unfortunately not much we can do to avoid this
        let (n, g) = (self.dim_generic(), self.grade_generic());
        let mut dst = AllocateBlade::<T,N,DimDiff<N,G>>::uninit(n, n.sub(g));

        //for convenience
        let (n, g, e) = (self.dim(), self.grade(), self.elements());
        let mut b = self.into_iter();

        //if the inverse of the psuedoscalar negates the psuedoscalar
        let neg = n & 0b10 != 0;

        if 2*g > n && neg {
            for i in 0..e { dst[i] = MaybeUninit::new(-b.next().unwrap()) }
        } else if 2*g == n && n!=0 {

            //for grades at the exact middle of a dimension, half gets negated, half gets copied

            //copy the bottom half, negate the top half
            for i in 0..e/2 { dst[e/2 + i] = MaybeUninit::new(b.next().unwrap()) }
            if neg {
                for i in 0..e/2 { dst[i] = MaybeUninit::new(-b.next().unwrap()) }
            } else {
                for i in 0..e/2 { dst[i] = MaybeUninit::new(b.next().unwrap()) }
            }

        } else {
            for i in 0..e { dst[i] = MaybeUninit::new(b.next().unwrap()) }
        }

        Blade { data: unsafe { dst.assume_init() } }

    }

}

#[cfg(test)]
mod tests {

    use super::*;

    use na::dimension::DimName;
    use crate::base::dim::{
        U0, U1, U2, U3, U4, U5, U6, U7, U8, U9
    };

    const N: usize = TEST_DIM;

    #[test]
    fn dual_inverse() {


        //for dynamic blades
        for n in 0..=N {
            for g in 0..=n {
                let b = BladeD::from_element(n, g, 0);
                assert_eq!(b, b.clone().dual().undual());
                assert_eq!(b, b.clone().undual().dual());
            }
        }

        //for static blades

        macro_rules! do_test {
            ($(($N:ident, $G:ident))*) => {
                $(
                    let b = Blade::<_,$N,$G>::from_element(0);
                    assert_eq!(b, b.dual().undual());
                    assert_eq!(b, b.undual().dual());
                )*
            }
        }

        do_test!(
            (U0, U0)
            (U1, U0) (U1, U1)
            (U2, U0) (U2, U1) (U2, U2)
            (U3, U0) (U3, U1) (U3, U2) (U3, U3)
            (U4, U0) (U4, U1) (U4, U2) (U4, U3) (U4, U4)
            (U5, U0) (U5, U1) (U5, U2) (U5, U3) (U5, U4) (U5, U5)
            (U6, U0) (U6, U1) (U6, U2) (U6, U3) (U6, U4) (U6, U5) (U6, U6)
            (U7, U0) (U7, U1) (U7, U2) (U7, U3) (U7, U4) (U7, U5) (U7, U6) (U7, U7)
            (U8, U0) (U8, U1) (U8, U2) (U8, U3) (U8, U4) (U8, U5) (U8, U6) (U8, U7) (U8, U8)
            (U9, U0) (U9, U1) (U9, U2) (U9, U3) (U9, U4) (U9, U5) (U9, U6) (U9, U7) (U9, U8) (U9, U9)
        );

    }

    #[test]
    fn puedovector_dual() {

        for n in 3..=N {

            let sign = if n&0b10 != 0 { -1 } else { 1 };

            let pv = BladeD::from_iterator(n, n-1, 1..);
            let v = BladeD::from_iterator(n, 1, 1..);

            assert_eq!(v, pv.clone().dual());
            assert_eq!(v.clone().undual(), pv);
            assert_eq!(v.clone().dual().as_slice(), pv.clone().undual().as_slice());

            assert_eq!(sign*&v, pv.clone().undual());
            assert_eq!(v.clone().dual(), sign*&pv);

        }

        macro_rules! do_test {
            ($($N:ident),*) => {
                $(
                    let sign = if $N::dim() & 0b10 != 0 { -1 } else { 1 };

                    let pv = PsuedoVecN::<_,$N>::from_iterator(1..);
                    let v = VecN::<_,$N>::from_iterator(1..);

                    assert_eq!(v, pv.clone().dual());
                    assert_eq!(v.clone().undual(), pv);
                    assert_eq!(v.clone().dual().as_slice(), pv.clone().undual().as_slice());

                    assert_eq!(sign*&v, pv.clone().undual());
                    assert_eq!(v.clone().dual(), sign*&pv);
                )*
            }
        }

        do_test!(U3, U4, U5, U6, U7, U8, U9);


    }


}
