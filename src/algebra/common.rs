
use super::*;

unsafe impl<T:AllocBlade<N,G>, N:Dim, G:Dim> Alloc<Blade<T,N,G>> for DefaultAllocator {
    type Scalar = T;
    type Shape = (N,G);
    type Buffer = AllocateBlade<T,N,G>;
    type Uninit = <AllocateBlade<T,N,G> as Storage<T>>::Uninit;

    fn shape(this: &Blade<T,N,G>) -> (N,G) { (this.dim_generic(), this.grade_generic()) }
    fn uninit((n,g): (N,G)) -> Self::Uninit { AllocateBlade::<T,N,G>::uninit(n,g) }
    unsafe fn assume_init(uninit: Self::Uninit) -> Blade<T,N,G> { Blade { data: uninit.assume_init() } }

}

unsafe impl<T:AllocEven<N>, N:Dim> Alloc<Even<T,N>> for DefaultAllocator {
    type Scalar = T;
    type Shape = N;
    type Buffer = AllocateEven<T,N>;
    type Uninit = <AllocateEven<T,N> as Storage<T>>::Uninit;

    fn shape(this: &Even<T,N>) -> N { this.dim_generic() }
    fn uninit(n: N) -> Self::Uninit { AllocateEven::<T,N>::uninit(n) }
    unsafe fn assume_init(uninit: Self::Uninit) -> Even<T,N> { Even { data: uninit.assume_init() } }

}

unsafe impl<T:AllocOdd<N>, N:Dim> Alloc<Odd<T,N>> for DefaultAllocator {
    type Scalar = T;
    type Shape = N;
    type Buffer = AllocateOdd<T,N>;
    type Uninit = <AllocateOdd<T,N> as Storage<T>>::Uninit;

    fn shape(this: &Odd<T,N>) -> N { this.dim_generic() }
    fn uninit(n: N) -> Self::Uninit { AllocateOdd::<T,N>::uninit(n) }
    unsafe fn assume_init(uninit: Self::Uninit) -> Odd<T,N> { Odd { data: uninit.assume_init() } }

}

unsafe impl<T:AllocMultivector<N>, N:Dim> Alloc<Multivector<T,N>> for DefaultAllocator {
    type Scalar = T;
    type Shape = N;
    type Buffer = AllocateMultivector<T,N>;
    type Uninit = <AllocateMultivector<T,N> as Storage<T>>::Uninit;

    fn shape(this: &Multivector<T,N>) -> N { this.dim_generic() }
    fn uninit(n: N) -> Self::Uninit { AllocateMultivector::<T,N>::uninit(n) }
    unsafe fn assume_init(uninit: Self::Uninit) -> Multivector<T,N> {
        Multivector { data: uninit.assume_init() }
    }

}

macro_rules! common_functions {

    //we put this here so that we can order things in the docs

    (false $ty:ident @grade_generic) => {};
    (true $ty:ident @grade_generic) => {
        ///
        /// Returns the [grade][1] of this Blade as an instance of the generic type `G`
        ///
        /// This is mostly used internally to unify the codebase between [`Const`] grades
        /// and [`Dynamic`] grades. Since `Dynamic` grades often require a `usize` input when
        /// `Const` grades do not, this allows a function to take a ZST for static Blades
        /// and to take a numeric value for dynamic ones
        ///
        #[doc = concat!("[1]: ", stringify!($ty), "::grade()")]
        pub fn grade_generic(&self) -> G { self.data.grade() }
    };

    (false $ty:ident @grade) => {};
    (true $ty:ident @grade) => {
        ///
        /// The grade of this blade
        ///
        /// This describes the "dimension" of the vector space this blade represents. Note that this
        /// is completely different that the [dimension][1] of the blade which describes the
        /// the dimension of the surrounding space the blade lives in.
        ///
        /// More concretely, the grade is the number of vector basis elements multiplied together
        /// to get a basis of this blade. So to get a blade of grade 3, you would need to
        /// wedge three vectors together.
        ///
        /// # Examples
        /// ```
        /// # use wedged::algebra::*;
        ///
        /// //All vectors are grade 1
        /// let v1 = Vec3::new(6, 2, 8);
        /// let v2 = Vec6::new(6, 2, 8, 3, 1, 8);
        /// let v3 = VecD::from_element(2, 0.0);
        ///
        /// assert_eq!(v1.grade(), 1);
        /// assert_eq!(v2.grade(), 1);
        /// assert_eq!(v3.grade(), 1);
        ///
        /// //All Bivectors are grade 2
        /// let b1 = BiVec4::new(6, 2, 8, 3, 1, 8);
        /// let b2 = BiVecD::from_element(3, 0.0);
        ///
        /// assert_eq!(b1.grade(), 2);
        /// assert_eq!(b2.grade(), 2);
        ///
        /// //Dynamic blades
        /// let blade1 = Blade6::from_element(5, 0.0);
        /// let blade2 = BladeD::from_element(4, 3, 0.0);
        ///
        /// assert_eq!(blade1.grade(), 5);
        /// assert_eq!(blade2.grade(), 3);
        ///
        /// ```
        ///
        #[doc = concat!("[1]: ", stringify!($ty), "::dim()")]
        pub fn grade(&self) -> usize { self.grade_generic().value() }
    };

    ($do_grade:tt $ty:ident) => {

        ///
        /// Returns the [dimension][1] of this value as an instance of the generic type `N`
        ///
        /// This is mostly used internally to unify the codebase between [`Const`] dimensions
        /// and [`Dynamic`] dimensions. Since `Dynamic` grades often require a `usize` input when
        /// `Const` grades do not, this allows a function to take a ZST for static dimensions
        /// and to take a numeric value for dynamic ones
        ///
        #[doc = concat!("[1]: ", stringify!($ty), "::dim()")]
        pub fn dim_generic(&self) -> N { self.data.dim() }

        common_functions!($do_grade $ty @grade_generic);

        ///
        /// The number of dimensions this value resides in
        ///
        /// Note that this differs from both the [grade](Blade::grade) and number of
        /// [elements][1]. Instead, this describes the dimension of the vector space
        /// generating the algebra this blade resides in.
        ///
        /// # Examples
        /// ```
        /// # use wedged::algebra::*;
        ///
        /// //All of these live in 3-dimensions
        /// let v = Vec3::new(3, 1, 4);
        /// let b = BiVec3::new(6, 2, 8);
        /// let r = Even3::new(1, 6, 1, 8);
        /// let m = Multivector3::new(0, 5, 7, 7, 2, 1, 5, 6);
        ///
        /// assert_eq!(v.dim(), 3);
        /// assert_eq!(b.dim(), 3);
        /// assert_eq!(r.dim(), 3);
        /// assert_eq!(m.dim(), 3);
        ///
        /// //whereas these are in 4D
        /// let v = Vec4::from_element(6);
        /// let b = BiVec4::from_element(2);
        /// let r = Even4::from_element(8);
        /// let m = Multivector4::from_element(3);
        ///
        /// assert_eq!(v.dim(), 4);
        /// assert_eq!(b.dim(), 4);
        /// assert_eq!(r.dim(), 4);
        /// assert_eq!(m.dim(), 4);
        ///
        /// ```
        ///
        #[doc = concat!("[1]: ", stringify!($ty), "::elements()")]
        pub fn dim(&self) -> usize { self.dim_generic().value() }

        common_functions!($do_grade $ty @grade);

        ///
        /// The number of coordinates this value has
        ///
        /// Note that for all values besides vectors and psuedovectors, this is _completely_
        /// different than the [dimension][1] which instead measures the dimension of the space
        /// the value lives in.
        ///
        /// - For [blades](Blade), this value is equal to number of combinations of size
        ///   `self.grade()` you can make from `self.dim()` basis vectors, ie
        ///   [`binom(self.dim(), self.grade())`](binom).
        /// - For [even](Even) values, the number of elements is `2^(self.dim()-1)` with the exception
        ///   of `1` when the dimension is `0`
        /// - For general [multivectors](Multivector), there are `2^self.dim()` components
        ///
        /// Finally, note that in all cases, the value returned is either a compile-time constant
        /// or cached as the length of some array, so there is no computational overhead to this
        /// function.
        ///
        /// # Examples
        /// ```
        /// # use wedged::algebra::*;
        ///
        /// let v = Vec4::from_element(0);
        /// let b = BiVec4::from_element(0);
        /// let r = Even4::from_element(0);
        /// let m = Multivector4::from_element(0);
        ///
        /// assert_eq!(v.elements(), 4); // (4 choose 1) = 4
        /// assert_eq!(b.elements(), 6); // (4 choose 2) = 6
        /// assert_eq!(r.elements(), 8); // 2^(4-1) = 8
        /// assert_eq!(m.elements(), 16); // 2^4 = 16
        ///
        /// ```
        ///
        #[doc = concat!("[1]: ", stringify!($ty), "::dim()")]
        pub fn elements(&self) -> usize { self.data.elements() }

        /// Borrows the components of this value as a slice
        pub fn as_slice(&self) -> &[T] { self.data.borrow() }

        /// Borrows the components of this value as a mutable slice
        pub fn as_mut_slice(&mut self) -> &mut [T] { self.data.borrow_mut() }

        /// Creates an iterator over references of each component
        pub fn iter(&self) -> Iter<T> { self.as_slice().iter() }

        /// Creates an iterator over mutable references of each component
        pub fn iter_mut(&mut self) -> IterMut<T> { self.as_mut_slice().iter_mut() }
    }
}

impl<T:AllocBlade<N,G>, N:Dim, G:Dim> Blade<T,N,G> {
    common_functions!(true Blade);
}

impl<T:AllocEven<N>,N:Dim> Even<T,N> {
    common_functions!(false Even);
}

impl<T:AllocOdd<N>,N:Dim> Odd<T,N> {
    common_functions!(false Odd);
}

impl<T:AllocMultivector<N>,N:Dim> Multivector<T,N> {
    common_functions!(false Multivector);
}


macro_rules! impl_basic_traits {
    () => {};
    (impl<T:$Alloc:ident, $($N:ident),*> $Ty:ident {} $($rest:tt)*) => {

        impl<T:$Alloc<$($N),*>+Clone, $($N:Dim),*> Clone for $Ty<T,$($N),*> {
            fn clone(&self) -> Self { $Ty { data: self.data.clone_storage() } }
            fn clone_from(&mut self, src: &Self) { self.data.clone_from_storage(&src.data) }
        }

        //TODO: once we have specialization, we can do fancy things to make the extra Self bound
        //unnecessary
        impl<T:$Alloc<$($N),*>+Copy, $($N:Dim),*> Copy for $Ty<T,$($N),*> where Allocate<Self>: Copy {}


        impl<T:$Alloc<$($N),*>, $($N:Dim),*> AsRef<[T]> for $Ty<T,$($N),*> {
            fn as_ref(&self) -> &[T] { self.data.as_ref() }
        }

        impl<T:$Alloc<$($N),*>, $($N:Dim),*> AsMut<[T]> for $Ty<T,$($N),*> {
            fn as_mut(&mut self) -> &mut [T] { self.data.as_mut() }
        }

        impl<T:$Alloc<$($N),*>, $($N:Dim),*> Borrow<[T]> for $Ty<T,$($N),*> {
            fn borrow(&self) -> &[T] { self.data.borrow() }
        }

        impl<T:$Alloc<$($N),*>, $($N:Dim),*> BorrowMut<[T]> for $Ty<T,$($N),*> {
            fn borrow_mut(&mut self) -> &mut [T] { self.data.borrow_mut() }
        }

        impl<T:$Alloc<$($N),*>+Eq, $($N:Dim),*> Eq for $Ty<T,$($N),*> {}

        impl<T:$Alloc<$($N),*>+Hash, $($N:Dim),*> Hash for $Ty<T,$($N),*> {
            fn hash<H:Hasher>(&self, h: &mut H) {
                T::hash_slice(self.borrow(), h)
            }
        }

        impl<T:$Alloc<$($N),*>, $($N:Dim),*> IntoIterator for $Ty<T,$($N),*> {
            type Item = T;
            type IntoIter = <Allocate<Self> as Storage<T>>::Iter;
            fn into_iter(self) -> Self::IntoIter {
                self.data.into_iter()
            }
        }

        impl<'a, T:$Alloc<$($N),*>, $($N:Dim),*> IntoIterator for &'a $Ty<T,$($N),*> {
            type Item = &'a T;
            type IntoIter = Iter<'a, T>;
            fn into_iter(self) -> Self::IntoIter { self.iter() }
        }

        impl<'a, T:$Alloc<$($N),*>, $($N:Dim),*> IntoIterator for &'a mut $Ty<T,$($N),*> {
            type Item = &'a mut T;
            type IntoIter = IterMut<'a, T>;
            fn into_iter(self) -> Self::IntoIter { self.iter_mut() }
        }

        impl<T:$Alloc<$($N),*>, $($N:DimName),*> FromIterator<T> for $Ty<T,$($N),*> {
            fn from_iter<I:IntoIterator<Item=T>>(iter: I) -> $Ty<T,$($N),*> {
                Self::from_iterator(iter.into_iter())
            }
        }

        impl<T:$Alloc<$($N),*>+Default, $($N:DimName),*> Default for $Ty<T,$($N),*> {
            fn default() -> $Ty<T,$($N),*> {
                Self::from_iterator(std::iter::repeat_with(|| T::default()))
            }
        }

        impl<T:$Alloc<$($N),*>+Debug, $($N:Dim),*> Debug for $Ty<T,$($N),*> {
            fn fmt(&self, f: &mut Formatter) -> FmtResult {
                Debug::fmt(self.as_slice(), f)
            }
        }

        impl_basic_traits!($($rest)*);

    }
}

impl_basic_traits!(
    impl<T:AllocBlade, N, G> Blade {}
    impl<T:AllocEven, N> Even {}
    impl<T:AllocOdd, N> Odd {}
    impl<T:AllocMultivector, N> Multivector {}
);

impl_eq!(
    Blade<T:AllocBlade,N1,G1>          == Blade<T:AllocBlade,N2,G2> with
    |self, rhs| self.shape_eq(rhs), self.as_slice(), rhs.as_slice();

    Even<T:AllocEven,N1>               == Even<T:AllocEven,N2> with
    |self, rhs| self.shape_eq(rhs), self.as_slice(), rhs.as_slice();

    Odd<T:AllocOdd,N1>                 == Odd<T:AllocOdd,N2> with
    |self, rhs| self.shape_eq(rhs), self.as_slice(), rhs.as_slice();

    Multivector<T:AllocMultivector,N1> == Multivector<T:AllocMultivector,N2> with
    |self, rhs| self.shape_eq(rhs), self.as_slice(), rhs.as_slice();
);

impl<T:AllocBlade<N,G>, N:Dim, G:Dim> Blade<T,N,G> {

    /// True if the grade if this blade is even
    #[inline(always)] pub fn even(&self) -> bool { self.grade()&1 == 0 }

    /// True if the grade if this blade is odd
    #[inline(always)] pub fn odd(&self) -> bool { self.grade()&1 == 1 }

    /// True if blades if this grade square to positive numbers
    #[inline(always)] pub fn pos_sig(&self) -> bool { self.grade()&2 == 0 }

    /// True if blades if this grade square to negative numbers
    #[inline(always)] pub fn neg_sig(&self) -> bool { self.grade()&2 != 0 }

}

impl<T1:AllocBlade<N1,G1>, N1:Dim, G1:Dim> Blade<T1,N1,G1> {

    ///Determines if the dimension and grade of two `Blade`s are equal
    pub fn shape_eq<T2:AllocBlade<N2,G2>, N2:Dim, G2:Dim>(&self, rhs: &Blade<T2,N2,G2>) -> bool {
        self.dim()==rhs.dim() && self.grade()==rhs.grade()
    }

}

impl<T:AllocEven<N>, N:Dim> Even<T,N> {

    /// Always true, but useful for macros
    pub fn even(&self) -> bool { true }

    /// Always false, but useful for macros
    pub fn odd(&self) -> bool { false }

}

impl<T1:AllocEven<N1>, N1:Dim> Even<T1,N1> {

    ///Determines if the dimension of two `Even`s are equal
    pub fn shape_eq<T2:AllocEven<N2>, N2:Dim>(&self, rhs: &Even<T2,N2>) -> bool {
        self.dim()==rhs.dim()
    }

}

impl<T:AllocOdd<N>, N:Dim> Odd<T,N> {

    /// Always false, but useful for macros
    pub fn even(&self) -> bool { false }

    /// Always true, but useful for macros
    pub fn odd(&self) -> bool { true }

}

impl<T1:AllocOdd<N1>, N1:Dim> Odd<T1,N1> {

    ///Determines if the dimension of two `Odd`s are equal
    pub fn shape_eq<T2:AllocOdd<N2>, N2:Dim>(&self, rhs: &Odd<T2,N2>) -> bool {
        self.dim()==rhs.dim()
    }

}

impl<T1:AllocMultivector<N1>, N1:Dim> Multivector<T1,N1> {

    ///Determines if the dimension of two `Multivectors`s are equal
    pub fn shape_eq<T2:AllocMultivector<N2>, N2:Dim>(&self, rhs: &Multivector<T2,N2>) -> bool {
        self.dim()==rhs.dim()
    }

}


#[cfg(test)]
mod tests{
    use super::*;

    const N: usize = TEST_DIM;

    #[test]
    fn grade() {

        for n in 0..=N {
            for g in 0..=N {
                let b = BladeD::from_element(n,g,0);
                assert_eq!(b.grade(), g);
            }
        }

        dim_name_test_loop!(
            |$N, $G| {
                let b = Blade::<_,$N,$G>::from_element(0);
                assert_eq!(b.grade(), $G::dim());
            }
        );
    }

    #[test]
    fn dim() {

        for n in 0..=N {
            for g in 0..=N {
                assert_eq!(BladeD::from_element(n,g,0).dim(), n);
            }
            assert_eq!(EvenD::from_element(n,0).dim(), n);
            assert_eq!(OddD::from_element(n,0).dim(), n);
            assert_eq!(MultivectorD::from_element(n,0).dim(), n);
        }

        dim_name_test_loop!(
            |$N, $G| {
                let n = $N::dim();
                assert_eq!(Blade::<_,$N,$G>::from_element(0).dim(), n);
            }
        );

        dim_name_test_loop!(
            |$N| {
                let n = $N::dim();
                assert_eq!(Even::<_,$N>::from_element(0).dim(), n);
                assert_eq!(Odd::<_,$N>::from_element(0).dim(), n);
                assert_eq!(Multivector::<_,$N>::from_element(0).dim(), n);
            }
        );
    }

    #[test]
    fn elements() {

        for n in 0..=N {
            for g in 0..=N {
                assert_eq!(BladeD::from_element(n,g,0).elements(), binom(n,g));
            }
            assert_eq!(EvenD::from_element(n,0).elements(), if n==0 {1} else {1 << (n-1)} );
            assert_eq!(OddD::from_element(n,0).elements(), if n==0 {0} else {1 << (n-1)} );
            assert_eq!(MultivectorD::from_element(n,0).elements(), 1<<n);
        }

        dim_name_test_loop!(
            |$N, $G| {
                let (n, g) = ($N::dim(), $G::dim());
                assert_eq!(Blade::<_,$N,$G>::from_element(0).elements(), binom(n, g));
            }
        );

        dim_name_test_loop!(
            |$N| {
                let n = $N::dim();
                assert_eq!(Even::<_,$N>::from_element(0).elements(), if n==0 {1} else {1 << (n-1)} );
                assert_eq!(Odd::<_,$N>::from_element(0).elements(), if n==0 {0} else {1 << (n-1)} );
                assert_eq!(Multivector::<_,$N>::from_element(0).elements(), 1<<n);
            }
        );
    }


}
