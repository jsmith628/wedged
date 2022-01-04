
use super::*;

macro_rules! norm_methods {
    () => {

        ///
        /// The sum of squares of each element
        ///
        /// Note that this does **not** take into account the conjugate of any
        /// complex elements. This is by explicit design for two reasons:
        /// 1. We can relax the [`ComplexField`] requirement and have more possibilies for scalars
        ///   types (like polynomials!).
        /// 2. For vectors, this is supposed to be the quadradic form of the underlying Clifford
        ///   algebra, and `zz̅` is not a valid quadradic form [1]
        ///
        /// [1]: https://en.wikipedia.org/wiki/Clifford_algebra#Complex_numbers
        ///
        pub fn norm_sqrd(&self) -> T::AllOutput where
            T: AllRefMul<T>, T::AllOutput: AddMonoid
        {
            self.iter().map(|t| t.ref_mul(t)).fold(T::AllOutput::zero(), |c,t| c+t)
        }

        //TODO: reevaluate the trait bounds... we may want to have these be real-valued instead

        ///
        /// The square root of the sum of squares of each element
        ///
        /// As with `norm_squared`, this does **not** take into account the complex conjugate
        /// even though [`ComplexField`] is a requirement.
        ///
        pub fn norm(&self) -> T::AllOutput where
            T: AllRefMul<T>, T::AllOutput: ComplexField
        {
            //TODO: optimize special case where there is only one element
            self.norm_sqrd().sqrt()
        }

        /// Divides `self` by its norm
        pub fn normalize(self) -> Self where T: RefComplexField
        {
            let l = self.norm();
            self / l
        }

        /// Divides `self` by its norm if it is non-zero
        pub fn try_normalize(self) -> Option<Self> where T: RefComplexField
        {
            let l = self.norm();
            if !l.is_zero() { Some(self / l) } else { None }
        }

        /// Divides `self` by its norm and returns both
        pub fn norm_and_normalize(self) -> (T, Self) where T:RefComplexField
        {
            let l = self.norm();
            let normalized = self / &l;
            (l, normalized)
        }

        /// Divides `self` by its norm and returns both if it is non-zero
        pub fn try_norm_and_normalize(self) -> Option<(T, Self)> where T:RefComplexField
        {
            let l = self.norm_sqrd();
            if !l.is_zero() {
                let l = l.sqrt();
                let normalized = self / &l;
                Some((l, normalized))
            } else {
                None
            }
        }

    }
}

impl<T:AllocBlade<N,G>, N:Dim, G:Dim> Blade<T,N,G> {

    ///
    /// Negates this Blade if its grade is odd
    ///
    /// This is helpful since commuting the wedge of a vector and a blade requires `g` swaps.
    /// This means that:
    /// - `v ^ B == B.involute() ^ v` and
    /// - `A ^ B == B.involute() ^ A.involute()`
    ///
    pub fn involute(self) -> Self where T: Neg<Output=T> {
        if (self.grade() & 0b01) != 0 { -self } else { self }
    }

    ///
    /// Effectively swaps the order of the vectors in each basis element
    ///
    /// This is the same and multiplying by `(-1)^(g(g-1)/2)` where `g = self.grade()`.
    ///
    /// The reverse function is useful as this effectively does the multiplicative inverse of each
    /// basis element. This way, for simple blades, `b * b.reverse() == b.norm_sqrd()` and for
    /// unit simple blades, this is the same as computing the inverse
    ///
    pub fn reverse(self) -> Self where T: Neg<Output=T> {
        if self.neg_sig() { -self } else { self }
    }

    norm_methods!();

}

macro_rules! involution {
    ($self:ident, $uninit:expr, $components:expr, $mask:expr) => {
        {
            //the destination
            let mut i = 0;
            let mut uninit = $uninit;

            //the data from self
            let mut iter = $self.into_iter();

            //iterate over every grade, negating every other blade
            for (g, count) in $components.enumerate() {

                //flip only the relevant blades
                if g&$mask != 0 {
                    for _ in 0..count {
                        uninit[i] = MaybeUninit::new(-iter.next().unwrap());
                        i+=1;
                    }
                } else {
                    for _ in 0..count {
                        uninit[i] = MaybeUninit::new(iter.next().unwrap());
                        i+=1;
                    }
                }
            }

            unsafe { Self { data: uninit.assume_init() } }
        }
    }
}

impl<T:AllocEven<N>, N:Dim> Even<T,N> {

    ///
    /// Swaps the order of the vectors in each basis element
    ///
    /// This is the same and multiplying by each component `(-1)^(g(g-1)/2)` where `g` is the
    /// grade of each basis element.
    ///
    /// The reverse function is useful as this effectively finds the multiplicative inverse of each
    /// basis element. This way, for invertible versers, `r * r.reverse() == r.norm_sqrd()` and for
    /// unit invertible versers, this is the same as computing the inverse
    ///
    /// Furthermore, for invertible rotors, this operation inverts the rotational action of this
    /// rotor without affecting the scaling action.
    ///
    pub fn reverse(self) -> Self where T: Neg<Output=T> {
        let n = self.dim();
        involution!(
            self,
            AllocateEven::<T,N>::uninit(self.dim_generic()),
            even_components_of(n), 0b1 //the iterator skips the odd grades, so we only need to have 0b1 as the mask
        )
    }

    ///
    /// Negates every odd-grade component of this rotor
    ///
    /// However, seeing as this is the even subalgebra, this does nothing and is
    /// only included for completeness and to simplify macros.
    ///
    pub fn involute(self) -> Self where T: Neg<Output=T> { self }

    norm_methods!();

}

impl<T:AllocOdd<N>, N:Dim> Odd<T,N> {

    ///
    /// Swaps the order of the vectors in each basis element
    ///
    /// This is the same and multiplying by each component `(-1)^(g(g-1)/2)` where `g` is the
    /// grade of each basis element.
    ///
    /// The reverse function is useful as this effectively finds the multiplicative inverse of each
    /// basis element. This way, for invertible versers, `r * r.reverse() == r.norm_sqrd()` and for
    /// unit invertible versers, this is the same as computing the inverse
    ///
    pub fn reverse(self) -> Self where T: Neg<Output=T> {
        let n = self.dim();
        involution!(
            self,
            AllocateOdd::<T,N>::uninit(self.dim_generic()),
            odd_components_of(n), 0b10
        )
    }

    ///
    /// Negates every odd-grade component of this rotor
    ///
    /// However, seeing as rotors are apart of the odd subspace, this just applies a negation
    /// and is just here for completeness
    ///
    pub fn involute(self) -> Self where T: Neg<Output=T> { -self }

    norm_methods!();

}

impl<T:AllocMultivector<N>, N:Dim> Multivector<T,N> {

    ///
    /// Swaps the order of the vectors in each basis element
    ///
    /// This is the same and multiplying by each component `(-1)^(g(g-1)/2)` where `g` is the
    /// grade of each basis element.
    ///
    pub fn reverse(self) -> Self where T: Neg<Output=T> {
        let n = self.dim();
        involution!(
            self,
            AllocateMultivector::<T,N>::uninit(self.dim_generic()),
            components_of(n), 0b10
        )
    }

    /// Negatates the components of odd grade
    pub fn involute(self) -> Self where T: Neg<Output=T> {
        let n = self.dim();
        involution!(
            self,
            AllocateMultivector::<T,N>::uninit(self.dim_generic()),
            components_of(n), 0b10
        )
    }

    norm_methods!();

}
