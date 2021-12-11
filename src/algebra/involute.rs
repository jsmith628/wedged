
use super::*;

macro_rules! norm_methods {
    () => {

        /// The sum of squares of each element
        pub fn norm_sqrd(&self) -> T::AllOutput where
            T: AllRefMul<T>, T::AllOutput: Zero + Add<Output=T::AllOutput>
        {
            self.iter().map(|t| t.ref_mul(t)).fold(T::AllOutput::zero(), |c,t| c+t)
        }

        /// The Euclidean norm of this `self`
        pub fn norm(&self) -> T where T: AllRefMul<T,AllOutput=T> + ComplexField {
            self.norm_sqrd().sqrt()
        }

        /// Divides `self` by its Euclidean norm
        pub fn normalize(self) -> Self where
            T: AllRefMul<T,AllOutput=T> + for<'a> Div<&'a T, Output=T> + ComplexField
        {
            let l = self.norm();
            self / &l
        }

        /// Divides `self` by its Euclidean norm
        pub fn norm_and_normalize(self) -> (T, Self) where
            T: AllRefMul<T,AllOutput=T> + for<'a> Div<&'a T, Output=T> + ComplexField
        {
            let l = self.norm();
            let normalized = self / &l;
            (l, normalized)
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
    /// unit simple blades, this is the same as computing the [inverse](Blade::inverse())
    ///
    pub fn reverse(self) -> Self where T: Neg<Output=T> {
        if (self.grade() & 0b10) != 0 { -self } else { self }
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
    /// unit invertible versers, this is the same as computing the [inverse](Even::inverse())
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
    /// unit invertible versers, this is the same as computing the [inverse](Even::inverse())
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
