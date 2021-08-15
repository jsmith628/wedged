
use super::*;
use na::Scalar;

pub use na::base::coordinates::*;

#[repr(C)]
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct ScalarCoords<T:Scalar> {
    value: T,
}

#[repr(C)]
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct BiVec4Coords<T:Scalar> {
    yz: T,
    zx: T,
    xy: T,
    xw: T,
    yw: T,
    zw: T,
}

#[repr(C)]
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct ReIm<T:Scalar> {
    re:T,
    im:T,
}

#[repr(C)]
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct WIJK<T:Scalar> {
    w:T,
    i:T,
    j:T,
    k:T
}

macro_rules! impl_coords {
    ($($Ty:ident = $Coords:ident;)*) => {
        $(
            impl<T:Scalar> Deref for $Ty<T> {
                type Target = $Coords<T>;
                fn deref(&self) -> &$Coords<T> {
                    unsafe {
                        &*(&self[0] as *const T as *const $Coords::<T>)
                    }
                }
            }

            impl<T:Scalar> DerefMut for $Ty<T> {
                fn deref_mut(&mut self) -> &mut $Coords<T> {
                    unsafe {
                        &mut *(&mut self[0] as *mut T as *mut $Coords::<T>)
                    }
                }
            }
        )*
    }
}

impl_coords! {

    //Scalars
    Scalar0 = ScalarCoords;
    Scalar1 = ScalarCoords;
    Scalar2 = ScalarCoords;
    Scalar3 = ScalarCoords;
    Scalar4 = ScalarCoords;
    Scalar5 = ScalarCoords;
    Scalar6 = ScalarCoords;

    //Vectors
    Vec1 = X;
    Vec2 = XY;
    Vec3 = XYZ;
    Vec4 = XYZW;
    Vec5 = XYZWA;
    Vec6 = XYZWAB;

    //BiVec4
    BiVec4 = BiVec4Coords;

    //Psuedovectors
    BiVec3   = XYZ;
    TriVec4  = XYZW;
    QuadVec5 = XYZWA;
    PentVec6 = XYZWAB;

    //Psuedoscalars
    BiVec2   = ScalarCoords;
    TriVec3  = ScalarCoords;
    QuadVec4 = ScalarCoords;
    PentVec5 = ScalarCoords;
    HexVec6  = ScalarCoords;

    //The even algebras as Complex numbers and quaternions
    Even2 = ReIm;
    Even3 = WIJK;

}
