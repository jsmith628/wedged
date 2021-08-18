
use super::*;

impl<T:AllocBlade<N,G>, N:Dim, G:Dim> Blade<T,N,G> where
    T:AllocBlade<N,DimDiff<N,G>>+Neg<Output=T>,
    N: DimSub<G>
{

    ///
    /// Computes the dual of this element in the current dimension
    ///
    /// This produces a blade representing the subspace(s) containing all vectors perpendicular
    /// to `self`. For example, the dual of a vector will give a psuedovector representing the
    /// hyperplane with the vector as its normal, and the dual of the psuedovector of a hyperplane
    /// will give its vector normal.
    ///
    /// This computation is equivalent to `self / I` where `I` is the psuedoscalar of the space,
    /// but due to symmetries in how the [basis blades](BasisBlade) are chosen, this _usually_
    /// is done with just a simple copy or negation of the components.
    ///
    /// In fact, the bases are chosen **specifically** so that the components of a psuedovector
    /// are the same as the components of its dual. Though, the converse is not always true
    ///
    /// # Examples
    /// ```
    /// # use galgebra::algebra::*;
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

        //there is unfortunately not much we can do to avoid this
        let (n, g) = (self.dim_generic(), self.grade_generic());
        let mut dst = AllocateBlade::<T,N,DimDiff<N,G>>::uninit(n, n.sub(g));

        //for convenience
        let (n, g, e) = (self.dim(), self.grade(), self.elements());
        let mut b = self.into_iter();

        //if the inverse of the psuedoscalar negates the psuedoscalar
        let neg = n & 0b10 == 1;

        if 2*g < n && neg {
            for i in 0..e { dst[i] = MaybeUninit::new(-b.next().unwrap()) }
        } else if 2*g == n && neg {

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
    /// Even though it sounds like it would be a complex inverse opperation, it is essentially
    /// just the [dual](Blade::dual()), but negated in certain dimensions.
    ///
    /// Specifially, whereas the _dual_ is found by `self / I`, the _undual_ is found by
    /// `self * I`. So in dimensions where `I⁻¹ == I`, this is the same as the dual, and in
    /// dimensions where `I⁻¹ == -I`, it is the negative dual.
    ///
    pub fn undual(self) -> DualBlade<T,N,G> {

        //there is unfortunately not much we can do to avoid this
        let (n, g) = (self.dim_generic(), self.grade_generic());
        let mut dst = AllocateBlade::<T,N,DimDiff<N,G>>::uninit(n, n.sub(g));

        //for convenience
        let (n, g, e) = (self.dim(), self.grade(), self.elements());
        let mut b = self.into_iter();

        //if the inverse of the psuedoscalar negates the psuedoscalar
        let neg = n & 0b10 == 1;

        if 2*g > n && neg {
            for i in 0..e { dst[i] = MaybeUninit::new(-b.next().unwrap()) }
        } else if 2*g == n {

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
