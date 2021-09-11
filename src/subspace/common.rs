
use super::*;

macro_rules! impl_common {
    ($($Ty:ident<T:$Alloc:ident, $($N:ident),*> = $Target:ident;)*) => {

        $(
            impl<T:$Alloc<$($N),*>, $($N:Dim),*> Deref for $Ty<T,$($N),*> {
                type Target = $Target<T,$($N),*>;
                fn deref(&self) -> &Self::Target { &self.data }
            }

            impl<T:$Alloc<$($N),*>, $($N:Dim),*> $Ty<T,$($N),*> {

                pub fn into_inner(self) -> $Target<T,$($N),*> { self.data }
                pub fn as_inner(&self) -> &$Target<T,$($N),*> { &self.data }
                pub fn from_unchecked(b: $Target<T,$($N),*>) -> Self { Self { data: b } }

            }

            impl<T:$Alloc<$($N),*>+Eq, $($N:Dim),*> Eq for $Ty<T,$($N),*> {}
            impl<T, U, $($N:Dim),*> PartialEq<$Ty<U,$($N),*>> for $Ty<T,$($N),*> where
                T:$Alloc<$($N),*>+PartialEq<U>,
                U:$Alloc<$($N),*>
            {
                fn eq(&self, rhs:&$Ty<U,$($N),*>) -> bool { self.data.eq(&rhs.data) }
                fn ne(&self, rhs:&$Ty<U,$($N),*>) -> bool { self.data.ne(&rhs.data) }
            }

            impl<T:$Alloc<$($N),*>, $($N:Dim),*> Index<usize> for $Ty<T,$($N),*> {
                type Output = T;
                fn index(&self, i:usize) -> &T { &self.data[i] }
            }

            impl<T:$Alloc<$($N),*>, $($N:Dim),*> AsRef<[T]> for $Ty<T,$($N),*> {
                fn as_ref(&self) -> &[T] { self.data.as_ref() }
            }

            impl<T:$Alloc<$($N),*>, $($N:Dim),*> AsRef<$Target<T,$($N),*>> for $Ty<T,$($N),*> {
                fn as_ref(&self) -> &$Target<T,$($N),*> { &self.data }
            }

            impl<T:$Alloc<$($N),*>, $($N:Dim),*> Borrow<[T]> for $Ty<T,$($N),*> {
                fn borrow(&self) -> &[T] { self.data.borrow() }
            }

            impl<T:$Alloc<$($N),*>, $($N:Dim),*> Borrow<$Target<T,$($N),*>> for $Ty<T,$($N),*> {
                fn borrow(&self) -> &$Target<T,$($N),*> { &self.data }
            }

            impl<T:$Alloc<$($N),*>, $($N:Dim),*> IntoIterator for $Ty<T,$($N),*> {
                type Item = T;
                type IntoIter = <$Target<T,$($N),*> as IntoIterator>::IntoIter;
                fn into_iter(self) -> Self::IntoIter { self.data.into_iter() }
            }

            impl<'a, T:$Alloc<$($N),*>, $($N:Dim),*> IntoIterator for &'a $Ty<T,$($N),*> {
                type Item = &'a T;
                type IntoIter = Iter<'a,T>;
                fn into_iter(self) -> Self::IntoIter { (&self.data).into_iter() }
            }

            impl<T:$Alloc<$($N),*>, $($N:Dim),*> From<$Ty<T,$($N),*>> for $Target<T,$($N),*> {
                fn from(x: $Ty<T,$($N),*>) -> $Target<T,$($N),*> { x.data }
            }

            impl<'a, T:$Alloc<$($N),*>, $($N:Dim),*> From<&'a $Ty<T,$($N),*>> for &'a $Target<T,$($N),*> {
                fn from(x: &'a $Ty<T,$($N),*>) -> &'a $Target<T,$($N),*> { &x.data }
            }

            impl<'a, T:$Alloc<$($N),*>, $($N:Dim),*> From<&'a mut $Ty<T,$($N),*>> for &'a mut $Target<T,$($N),*> {
                fn from(x: &'a mut $Ty<T,$($N),*>) -> &'a mut $Target<T,$($N),*> { &mut x.data }
            }

            impl<T:$Alloc<$($N),*>, $($N:Dim),*> MultivectorSrc for $Ty<T,$($N),*> {

                type Scalar = T;
                type Dim = N;
                type Shape = <$Target<T,$($N),*> as MultivectorSrc>::Shape;

                fn dim(&self) -> Self::Dim { self.data.dim_generic() }
                fn elements(&self) -> usize { self.data.elements() }
                fn subspace(&self) -> Subspace { self.data.subspace() }
                fn shape(&self) -> Self::Shape { self.data.shape() }

                fn get(&self, i:usize) -> &Self::Scalar { self.data.get(i) }
                fn basis(&self, i:usize) -> BasisBlade { self.data.basis(i) }

            }

            impl<'a, T:$Alloc<$($N),*>, $($N:Dim),*> MultivectorSrc for &'a $Ty<T,$($N),*> {

                type Scalar = T;
                type Dim = N;
                type Shape = <$Target<T,$($N),*> as MultivectorSrc>::Shape;

                fn dim(&self) -> Self::Dim { self.data.dim_generic() }
                fn elements(&self) -> usize { self.data.elements() }
                fn subspace(&self) -> Subspace { self.data.subspace() }
                fn shape(&self) -> Self::Shape { self.data.shape() }

                fn get(&self, i:usize) -> &Self::Scalar { self.data.get(i) }
                fn basis(&self, i:usize) -> BasisBlade { self.data.basis(i) }

            }

            impl<T:$Alloc<$($N),*>, $($N:Dim),*> MultivectorDst for $Ty<T,$($N),*> {

                type Uninit = <$Target<T,$($N),*> as MultivectorDst>::Uninit;

                fn subspace_of(shape: Self::Shape) -> Subspace {
                    <$Target<T,$($N),*> as MultivectorDst>::subspace_of(shape)
                }

                fn uninit(shape: Self::Shape) -> Self::Uninit {
                    <$Target<T,$($N),*> as MultivectorDst>::uninit(shape)
                }

                unsafe fn assume_init(uninit: Self::Uninit) -> Self {
                    Self { data: <$Target<T,$($N),*> as MultivectorDst>::assume_init(uninit) }
                }

                fn index_of(basis: BasisBlade, shape: Self::Shape) -> Option<(usize, bool)> {
                    <$Target<T,$($N),*> as MultivectorDst>::index_of(basis, shape)
                }

            }


        )*

    }
}

macro_rules! impl_fmt {

    (; $($ty:tt)*) => {};
    ($Fmt0:ident $($Fmt:ident)+; $($ty:tt)*) => {
        impl_fmt!($Fmt0; $($ty)*);
        impl_fmt!($($Fmt)*; $($ty)*);
    };

    ($($Fmt:ident)*; ) => {};
    ($Fmt:ident; $Ty:ident<T:$Alloc:ident,$($N:ident),*> $($rest:tt)*) => {

        impl<'a, T:$Alloc<$($N),*>+$Fmt, $($N:Dim),*> $Fmt for $Ty<T,$($N),*> {
            fn fmt(&self, f: &mut Formatter) -> FmtResult { $Fmt::fmt(&self.data, f) }
        }

        impl_fmt!($Fmt; $($rest)*);
    };
}

impl_common!(
    SimpleBlade<T:AllocBlade,N,G> = Blade;
    UnitBlade<T:AllocBlade,N,G> = Blade;
    Rotor<T:AllocEven,N> = Even;
    Reflector<T:AllocOdd,N> = Odd;
);

impl_fmt!(
    Debug Display Binary Octal LowerHex UpperHex LowerExp UpperExp;
    SimpleBlade<T:AllocBlade,N,G>
    UnitBlade<T:AllocBlade,N,G>
    Rotor<T:AllocEven,N>
    Reflector<T:AllocOdd,N>
);

impl<T:AllocVersor<N>, N:Dim> Versor<T,N> {

    pub fn even(&self) -> bool {
        match self {
            Versor::Even(_) => true,
            Versor::Odd(_) => false,
        }
    }

    pub fn odd(&self) -> bool {
        match self {
            Versor::Even(_) => false,
            Versor::Odd(_) => true,
        }
    }
    
}

impl<T:AllocVersor<N>+Eq, N:Dim> Eq for Versor<T,N> {}
impl<T:AllocVersor<N>+PartialEq<U>, U:AllocVersor<N>, N:Dim> PartialEq<Versor<U,N>> for Versor<T,N> {

    //NOTE: theoretically, an even versor _can_ eq an odd versor if they are both zero,
    //However, we require that all versors have norm 1, so this is impossible under normal operation

    fn eq(&self, rhs: &Versor<U,N>) -> bool {
        match (self, rhs) {
            (Versor::Even(r1), Versor::Even(r2)) => r1.eq(r2),
            (Versor::Odd(r1), Versor::Odd(r2)) => r1.eq(r2),
            _ => false
        }
    }

    fn ne(&self, rhs: &Versor<U,N>) -> bool {
        match (self, rhs) {
            (Versor::Even(r1), Versor::Even(r2)) => r1.ne(r2),
            (Versor::Odd(r1), Versor::Odd(r2)) => r1.ne(r2),
            _ => true
        }
    }
}

macro_rules! impl_versor_fmt {
    ($($Fmt:ident)*) => {

        $(
            impl<T:AllocEven<N>+AllocOdd<N>+$Fmt, N:Dim> $Fmt for Versor<T,N> {
                fn fmt(&self, f: &mut Formatter) -> FmtResult {
                    match self {
                        Versor::Even(r) => $Fmt::fmt(r, f),
                        Versor::Odd(r) => $Fmt::fmt(r, f)
                    }
                }
            }
        )*

    }
}

impl_versor_fmt!(Debug Display Binary Octal LowerHex UpperHex LowerExp UpperExp);
