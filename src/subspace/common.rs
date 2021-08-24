
use super::*;

macro_rules! impl_deref {
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

            impl<T:$Alloc<$($N),*>, $($N:Dim),*> Copy for $Ty<T,$($N),*> where $Target<T,$($N),*>:Copy {}
            impl<T:$Alloc<$($N),*>, $($N:Dim),*> Clone for $Ty<T,$($N),*> where $Target<T,$($N),*>:Clone {
                fn clone(&self) -> Self { Self { data: self.data.clone() } }
                fn clone_from(&mut self, src:&Self) { self.data.clone_from(&src.data) }
            }

            impl<T:$Alloc<$($N),*>+Eq, $($N:Dim),*> Eq for $Ty<T,$($N),*> {}
            impl<T, U, $($N:Dim),*> PartialEq<$Ty<U,$($N),*>> for $Ty<T,$($N),*> where
                T:$Alloc<$($N),*>+PartialEq<U>,
                U:$Alloc<$($N),*>
            {
                fn eq(&self, rhs:&$Ty<U,$($N),*>) -> bool { self.data.eq(&rhs.data) }
                fn ne(&self, rhs:&$Ty<U,$($N),*>) -> bool { self.data.ne(&rhs.data) }
            }

            impl<T:$Alloc<$($N),*>+Hash, $($N:Dim),*> Hash for $Ty<T,$($N),*>{
                fn hash<H:Hasher>(&self, h: &mut H) { self.data.hash(h) }
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

impl_deref!(
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
