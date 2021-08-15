
use super::*;

macro_rules! norm_methods {
    () => {

        /// The sum of squares of each element
        pub fn norm_sqrd(&self) -> T::Output where
            T: RefMul<T>, T::Output: Zero + Add<Output=T::Output>
        {
            self.iter().map(|t| t.ref_mul(t)).fold(T::Output::zero(), |c,t| c+t)
        }

        /// The Euclidean norm of this `self`
        pub fn norm(&self) -> T where T: RefMul<T,Output=T> + ComplexField {
            self.norm_sqrd().sqrt()
        }

        /// Divides `self` by its Euclidean norm
        pub fn normalize(self) -> Self where
            T: RefMul<T,Output=T> + for<'a> Div<&'a T, Output=T> + ComplexField
        {
            let l = self.norm();
            self / &l
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

    ///
    /// The multiplicative inverse of this blade
    ///
    /// NOTE: this only works for _simple_ blades, ie, those that can be written as the product
    /// of vectors. For non-simple blades, it only computes the [reverse](Blade::reverse())
    /// divided by the [square norm](Blade::norm_sqrd). For blades up to 3D, this isn't a worry,
    /// but bivectors in 4D are a notable exception, as `e₁₂ + e₃₄` cannot be factored.
    ///
    pub fn inverse(self) -> Self where
        T: Zero + Neg<Output=T> + Add<Output=T> + RefMul<T,Output=T> + for<'a> Div<&'a T, Output=T>
    {
        let l = self.norm_sqrd();
        self.reverse() / &l
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

                //flip only every other blade
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
    /// basis element. This way, for invertible rotors, `r * r.reverse() == r.norm_sqrd()` and for
    /// unit invertible rotors, this is the same as computing the [inverse](Even::inverse())
    ///
    /// Furthermore, for invertible rotors, this operation inverts the rotational action of this
    /// rotor without affecting the scaling action.
    ///
    pub fn reverse(self) -> Self where T: Neg<Output=T> {
        let n = self.dim();
        involution!(
            self,
            AllocateEven::<T,N>::uninit(self.dim_generic()),
            even_components_in(n), 0b10
        )
    }

    ///
    /// Negates every odd-grade component of this rotor
    ///
    /// However, seeing as rotors are apart of the even subalgebra, this does nothing and is
    /// only included for completeness and to simplify macros.
    ///
    pub fn involute(self) -> Self where T: Neg<Output=T> { self }

    ///
    /// The multiplicative inverse of this rotor
    ///
    /// NOTE: this only works for _invertible_ rotors. For non-invertible rotors, it only computes
    /// the [reverse](Even::reverse) divided by the [square norm](Even::norm_sqrd()). Up to 4D,
    /// this is not an issue, as all non-zero rotors in 1-3D are invertible, but starting in four
    /// dimensions, there will always be values such as `1 + e₁₂₃₄` that cannot be inverted.
    ///
    pub fn inverse(self) -> Self where
        T: Zero + Neg<Output=T> + Add<Output=T> + RefMul<T,Output=T> + for<'a> Div<&'a T, Output=T>
    {
        let l = self.norm_sqrd();
        self.reverse() / &l
    }

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
            components_in(n), 0b10
        )
    }

    /// Negatates the components of odd grade
    pub fn involute(self) -> Self where T: Neg<Output=T> {
        let n = self.dim();
        involution!(
            self,
            AllocateMultivector::<T,N>::uninit(self.dim_generic()),
            components_in(n), 0b10
        )
    }

    norm_methods!();

}
