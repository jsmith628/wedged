
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

impl<T:Alloc<N,G>, N:DimName, G:DimName> Blade<T,N,G> {

    pub fn from_iterator<I:IntoIterator<Item=T>>(iter: I) -> Self {
        Self::from_iter_generic(N::name(), G::name(), iter)
    }

    pub fn from_index_fn<F: FnMut(usize)->T>(f: F) -> Self {
        Self::from_index_fn_generic(N::name(), G::name(), f)
    }

    pub fn from_element(x:T) -> Self where T:Clone {
        Self::from_element_generic(N::name(), G::name(), x)
    }

    pub fn zeroed() -> Self where T:Zero {
        Self::zeroed_generic(N::name(), G::name())
    }

}

impl<T:Alloc<Dynamic,G>, G:DimName> Blade<T,Dynamic,G> {

    pub fn from_iterator<I:IntoIterator<Item=T>>(n:usize, iter: I) -> Self {
        Self::from_iter_generic(Dynamic::new(n), G::name(), iter)
    }

    pub fn from_index_fn<F: FnMut(usize)->T>(n:usize, f: F) -> Self {
        Self::from_index_fn_generic(Dynamic::new(n), G::name(), f)
    }

    pub fn from_element(n:usize, x:T) -> Self where T:Clone {
        Self::from_element_generic(Dynamic::new(n), G::name(), x)
    }

    pub fn zeroed(n:usize) -> Self where T:Zero {
        Self::zeroed_generic(Dynamic::new(n), G::name())
    }

}

impl<T:Alloc<N,Dynamic>, N:DimName> Blade<T,N,Dynamic> {

    pub fn from_iterator<I:IntoIterator<Item=T>>(g:usize, iter: I) -> Self {
        Self::from_iter_generic(N::name(), Dynamic::new(g), iter)
    }

    pub fn from_index_fn<F: FnMut(usize)->T>(g:usize, f: F) -> Self {
        Self::from_index_fn_generic(N::name(), Dynamic::new(g), f)
    }

    pub fn from_element(g:usize, x:T) -> Self where T:Clone {
        Self::from_element_generic(N::name(), Dynamic::new(g), x)
    }

    pub fn zeroed(g:usize) -> Self where T:Zero {
        Self::zeroed_generic(N::name(), Dynamic::new(g))
    }

}

impl<T:Alloc<Dynamic,Dynamic>> Blade<T,Dynamic,Dynamic> {

    pub fn from_iterator<I:IntoIterator<Item=T>>(n:usize, g:usize, iter: I) -> Self {
        Self::from_iter_generic(Dynamic::new(n), Dynamic::new(g), iter)
    }

    pub fn from_index_fn<F: FnMut(usize)->T>(n:usize, g:usize, f: F) -> Self {
        Self::from_index_fn_generic(Dynamic::new(n), Dynamic::new(g), f)
    }

    pub fn from_element(n:usize, g:usize, x:T) -> Self where T:Clone {
        Self::from_element_generic(Dynamic::new(n), Dynamic::new(g), x)
    }

    pub fn zeroed(n:usize, g:usize) -> Self where T:Zero {
        Self::zeroed_generic(Dynamic::new(n), Dynamic::new(g))
    }

}

macro_rules! impl_static_constructors {
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

impl_static_constructors!{

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
