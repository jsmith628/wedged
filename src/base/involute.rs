
use super::*;

macro_rules! norm_methods {
    () => {

        pub fn norm_sqrd(&self) -> T::Output where
            T: RefMul<T>, T::Output: Zero + Add<Output=T::Output>
        {
            self.iter().map(|t| t.ref_mul(t)).fold(T::Output::zero(), |c,t| c+t)
        }

        pub fn norm(&self) -> T where T: RefMul<T,Output=T> + ComplexField {
            self.norm_sqrd().sqrt()
        }

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
    /// Negates this blade if its grade is odd
    ///
    /// This is helpful since commuting the wedge of a vector and a blade requires `g` swaps
    /// implying that both
    /// - `v ^ B == B.involute() ^ v` and
    /// - `A ^ B == B.involute() ^ A.involute()`
    ///
    pub fn involute(self) -> Self where T: Neg<Output=T> {
        if (self.grade() & 0b01) != 0 { -self } else { self }
    }

    pub fn reverse(self) -> Self where T: Neg<Output=T> {
        if (self.grade() & 0b10) != 0 { -self } else { self }
    }

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

impl<T:AllocRotor<N>, N:Dim> Rotor<T,N> {

    pub fn reverse(self) -> Self where T: Neg<Output=T> {
        let n = self.dim();
        involution!(
            self,
            AllocateRotor::<T,N>::uninit(self.dim_generic()),
            even_components_in(n), 0b10
        )
    }

    //does nothing since all bases in Rotors are even
    pub fn involute(self) -> Self where T: Neg<Output=T> { self }

    pub fn inverse(self) -> Self where
        T: Zero + Neg<Output=T> + Add<Output=T> + RefMul<T,Output=T> + for<'a> Div<&'a T, Output=T>
    {
        let l = self.norm_sqrd();
        self.reverse() / &l
    }

    norm_methods!();

}

impl<T:AllocMultivector<N>, N:Dim> Multivector<T,N> {

    pub fn reverse(self) -> Self where T: Neg<Output=T> {
        let n = self.dim();
        involution!(
            self,
            AllocateMultivector::<T,N>::uninit(self.dim_generic()),
            components_in(n), 0b10
        )
    }

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
