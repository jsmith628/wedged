
use crate::blade::Blade;

use na::dimension::{
    Dynamic,
    DimNameDiff,
    U0, U1, U2, U3, U4, U5, U6
};


macro_rules! impl_constructors {
    ($($ty:ident::new($($arg:ident),*);)*) => {
        $(
            impl<T> $ty<T> {
                pub fn new($($arg: T),*) -> $ty<T> {
                    $ty { data: [ $($arg),* ] }
                }
            }
        )*
    }
}

impl_constructors!{

    Vec1::new(x);
    Vec2::new(x,y);
    Vec3::new(x,y,z);
    Vec4::new(x,y,z,w);
    Vec5::new(x,y,z,w,a);
    Vec6::new(x,y,z,w,a,b);

    BiVec2::new(x);
    BiVec3::new(x,y,z);
    BiVec4::new(e23,e31,e12,e14,e24,e34);
    BiVec5::new(e23,e31,e12,e14,e24,e34,e15,e25,e35,e45);
    BiVec6::new(e23,e31,e12,e14,e24,e34,e15,e25,e35,e45,e16,e26,e36,e46,e56);

    TriVec3::new(x);
    TriVec4::new(x,y,z,w);
    TriVec5::new(e145, e245, e345, e235, e315, e125, e324, e134, e214, e123);
    TriVec6::new(
        e145, e245, e345, e235, e315, e125, e324, e134, e214, e123,
        e326, e136, e216, e416, e426, e436, e516, e526, e536, e546
    );

    QuadVec4::new(x);
    QuadVec5::new(x,y,z,w,a);
    QuadVec6::new(
        e4156, e4256, e4356, e3256, e1356, e2156, e2346, e3146, e1246, e2136, e3245, e1345, e2145, e1235, e2134
    );

    PentVec5::new(x);
    PentVec6::new(x,y,z,w,a,b);

    HexVec6::new(x);

}


pub type Scalar<T,N> = Blade<T,N,U0>;
pub type Scalar0<T> = Scalar<T,U0>;
pub type Scalar1<T> = Scalar<T,U1>;
pub type Scalar2<T> = Scalar<T,U2>;
pub type Scalar3<T> = Scalar<T,U3>;
pub type Scalar4<T> = Scalar<T,U4>;
pub type Scalar5<T> = Scalar<T,U5>;
pub type Scalar6<T> = Scalar<T,U6>;
pub type ScalarD<T> = Scalar<T,Dynamic>;

pub type VecN<T,N> = Blade<T,N,U1>;
pub type Vec1<T> = VecN<T,U1>;
pub type Vec2<T> = VecN<T,U2>;
pub type Vec3<T> = VecN<T,U3>;
pub type Vec4<T> = VecN<T,U4>;
pub type Vec5<T> = VecN<T,U5>;
pub type Vec6<T> = VecN<T,U6>;
pub type VecD<T> = VecN<T,Dynamic>;

pub type BiVecN<T,N> = Blade<T,N,U2>;
pub type BiVec2<T> = BiVecN<T,U2>;
pub type BiVec3<T> = BiVecN<T,U3>;
pub type BiVec4<T> = BiVecN<T,U4>;
pub type BiVec5<T> = BiVecN<T,U5>;
pub type BiVec6<T> = BiVecN<T,U6>;
pub type BiVecD<T> = BiVecN<T,Dynamic>;

pub type TriVecN<T,N> = Blade<T,N,U3>;
pub type TriVec3<T> = TriVecN<T,U3>;
pub type TriVec4<T> = TriVecN<T,U4>;
pub type TriVec5<T> = TriVecN<T,U5>;
pub type TriVec6<T> = TriVecN<T,U6>;
pub type TriVecD<T> = TriVecN<T,Dynamic>;

pub type QuadVecN<T,N> = Blade<T,N,U4>;
pub type QuadVec4<T> = QuadVecN<T,U4>;
pub type QuadVec5<T> = QuadVecN<T,U5>;
pub type QuadVec6<T> = QuadVecN<T,U6>;
pub type QuadVecD<T> = QuadVecN<T,Dynamic>;

pub type PentVecN<T,N> = Blade<T,N,U5>;
pub type PentVec5<T> = PentVecN<T,U5>;
pub type PentVec6<T> = PentVecN<T,U6>;
pub type PentVecD<T> = PentVecN<T,Dynamic>;

pub type HexVecN<T,N> = Blade<T,N,U6>;
pub type HexVec6<T> = HexVecN<T,U6>;
pub type HexVecD<T> = HexVecN<T,Dynamic>;

pub type PsuedoScalarN<T,N> = Blade<T,N,N>;
pub type PsuedoVecN<T,N> = Blade<T,N,DimNameDiff<N,U1>>;
pub type PsuedoBiVecN<T,N> = Blade<T,N,DimNameDiff<N,U2>>;
pub type PsuedoTriVecN<T,N> = Blade<T,N,DimNameDiff<N,U3>>;
pub type PsuedoQuadVecN<T,N> = Blade<T,N,DimNameDiff<N,U4>>;
pub type PsuedoPentVecN<T,N> = Blade<T,N,DimNameDiff<N,U5>>;
pub type PsuedoHexVecN<T,N> = Blade<T,N,DimNameDiff<N,U6>>;
