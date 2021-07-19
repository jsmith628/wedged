
use super::*;

impl<T:Alloc<N,G>, N:Dim, G:Dim> Blade<T,N,G> {

    pub fn from_iter_generic<I:IntoIterator<Item=T>>(n:N, g:G, iter: I) -> Self {
        Blade { data: Allocate::<T,N,G>::from_iterator(n, g, iter) }
    }

    pub fn from_index_fn_generic<F: FnMut(usize)->T>(n:N, g:G, f: F) -> Self {
        Self::from_iter_generic(n, g, (0..).into_iter().map(f))
    }

    pub fn from_element_generic(n:N, g:G, x:T) -> Self where T:Clone {
        Self::from_iter_generic(n, g, repeat(x))
    }

    pub fn zeroed_generic(n:N, g:G) -> Self where T:Zero {
        Self::from_iter_generic(n, g, repeat_with(|| T::zero()))
    }

}

macro_rules! impl_general_constructors {
    ($(
        pub fn new($($args:tt)*) -> Self { Self::new_generic($($call:tt)*) }
    )*) => {

        $(
            ///
            ///Constructs a blade with elements from an iterator
            ///
            ///Panics if the iterator has too few elements to fill in the blade
            ///
            pub fn from_iterator<I:IntoIterator<Item=T>>($($args)* iter: I) -> Self {
                Self::from_iter_generic($($call)*, iter)
            }

            ///Constructs a blade from a function mapping an index to an element
            pub fn from_index_fn<F: FnMut(usize)->T>($($args)* f: F) -> Self {
                Self::from_index_fn_generic($($call)*, f)
            }

            ///Constructs a blade where every component is the given element
            pub fn from_element($($args)* x:T) -> Self where T:Clone {
                Self::from_element_generic($($call)*, x)
            }

            ///Constructs a blade with all components set to [zero](Zero::zero)
            pub fn zeroed($($args)*) -> Self where T:Zero {
                Self::zeroed_generic($($call)*)
            }

        )*

    };
}

///Constructors for statically sized blades
impl<T:Alloc<N,G>, N:DimName, G:DimName> Blade<T,N,G> {

    impl_general_constructors!(
        pub fn new() -> Self {
            Self::new_generic(N::name(), G::name())
        }
    );

}

///Constructors for blades with dynamic dimension
impl<T:Alloc<Dynamic,G>, G:DimName> Blade<T,Dynamic,G> {

    impl_general_constructors!(
        pub fn new(n:usize,) -> Self {
            Self::new_generic(Dynamic::new(n), G::name())
        }
    );

}

///Constructors for blades with dynamic grade
impl<T:Alloc<N,Dynamic>, N:DimName> NBlade<T,N> {

    impl_general_constructors!(
        pub fn new(g:usize,) -> Self {
            Self::new_generic(N::name(), Dynamic::new(g))
        }
    );

}

///Constructors for blades with dynamic dimension and grade
impl<T:Alloc<Dynamic,Dynamic>> DBlade<T> {

    impl_general_constructors!(
        pub fn new(n:usize,g:usize,) -> Self {
            Self::new_generic(Dynamic::new(n), Dynamic::new(g))
        }
    );

}

macro_rules! impl_specific_constructors {
    ($($ty:ident::new($($arg:ident),*);)*) => {
        $(
            impl<T> $ty<T> {
                #[doc = concat!(
                    "Constructs a [`", stringify!($ty), "`] directly from components"
                )]
                pub fn new($($arg: T),*) -> $ty<T> {
                    $ty { data: [ $($arg),* ] }
                }
            }
        )*
    }
}

impl_specific_constructors!{

    Vec1::new(x);
    Vec2::new(x,y);
    Vec3::new(x,y,z);
    Vec4::new(x,y,z,w);
    Vec5::new(x,y,z,w,a);
    Vec6::new(x,y,z,w,a,b);

    BiVec2::new(x);
    BiVec3::new(x,y,z);
    BiVec4::new(yz,zx,xy,xw,yw,zw);
    BiVec5::new(yz,zx,xy,xw,yw,zw,xa,ya,za,wa);
    BiVec6::new(yz,zx,xy,xw,yw,zw,xa,ya,za,wa,xb,yb,zb,wb,ab);

    TriVec3::new(x);
    TriVec4::new(x,y,z,w);
    TriVec5::new(yz,zx,xy,xw,yw,zw,xa,ya,za,wa);
    TriVec6::new(
        e145, e245, e345, e235, e315, e125, e324, e134, e214, e123,
        e326, e136, e216, e416, e426, e436, e516, e526, e536, e546
    );

    QuadVec4::new(x);
    QuadVec5::new(x,y,z,w,a);
    QuadVec6::new(yz,zx,xy,xw,yw,zw,xa,ya,za,wa,xb,yb,zb,wb,ab);

    PentVec5::new(x);
    PentVec6::new(x,y,z,w,a,b);

    HexVec6::new(x);

}
