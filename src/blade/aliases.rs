
use super::*;

pub type NBlade<T,N> = Blade<T,N,Dynamic>;
pub type DBlade<T> = Blade<T,Dynamic,Dynamic>;

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
