//!
//! Structs to dereference the algebraic types into to access their elements as if they
//! were fields.
//!
//! This module mostly just wraps [`na::base::coordinates`], but a couple extra structs were added
//! in order to support some of the structures unique to this crate
//!

use std::ops::{Deref, DerefMut};

use na::Scalar;

use crate::algebra::*;
pub use na::base::coordinates::*;

/// Fields for scalar and psuedoscalar types
#[repr(C)]
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct ScalarCoords<T:Scalar> {
    pub value: T,
}

/// Fields specifically for 4D bivectors
#[repr(C)]
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct BiVec4Coords<T:Scalar> {
    pub yz: T,
    pub zx: T,
    pub xy: T,
    pub xw: T,
    pub yw: T,
    pub zw: T,
}

/// Fields for 2D [`Even`]s that emulate the components of complex numbers
#[repr(C)]
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct ReIm<T:Scalar> {
    pub re:T,
    pub im:T,
}

///
/// Fields for 3D [`Even`]s that emulate the components of quaternions
///
/// The order here is different from `nalgebra`'s [quaternions](na::geometry::Quaternion).
/// (`nalgebra` uses [ijkw](IJKW) order)
///
#[repr(C)]
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct WIJK<T:Scalar> {
    pub w:T,
    pub i:T,
    pub j:T,
    pub k:T
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
