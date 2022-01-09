
use super::*;

///An N-dimensional blade with a dynamic grade
pub type BladeN<T,N> = Blade<T,N,Dynamic>;
///A 0-dimensional blade with a dynamic grade
pub type Blade0<T> = Blade<T,U0,Dynamic>;
///A 1-dimensional blade with a dynamic grade
pub type Blade1<T> = Blade<T,U1,Dynamic>;
///A 2-dimensional blade with a dynamic grade
pub type Blade2<T> = Blade<T,U2,Dynamic>;
///A 3-dimensional blade with a dynamic grade
pub type Blade3<T> = Blade<T,U3,Dynamic>;
///A 4-dimensional blade with a dynamic grade
pub type Blade4<T> = Blade<T,U4,Dynamic>;
///A 5-dimensional blade with a dynamic grade
pub type Blade5<T> = Blade<T,U5,Dynamic>;
///A 6-dimensional blade with a dynamic grade
pub type Blade6<T> = Blade<T,U6,Dynamic>;
///A blade with a dynamic dimension and grade
pub type BladeD<T> = Blade<T,Dynamic,Dynamic>;

///A 0-dimensional rotor
pub type Even0<T> = Even<T,U0>;
///A 1-dimensional rotor
pub type Even1<T> = Even<T,U1>;
///A 2-dimensional rotor
pub type Even2<T> = Even<T,U2>;
///A 3-dimensional rotor
pub type Even3<T> = Even<T,U3>;
///A 4-dimensional rotor
pub type Even4<T> = Even<T,U4>;
///A 5-dimensional rotor
pub type Even5<T> = Even<T,U5>;
///A 6-dimensional rotor
pub type Even6<T> = Even<T,U6>;
///A rotor with dynamic dimension
pub type EvenD<T> = Even<T,Dynamic>;

///A 0-dimensional odd value
pub type Odd0<T> = Odd<T,U0>;
///A 1-dimensional odd value
pub type Odd1<T> = Odd<T,U1>;
///A 2-dimensional odd value
pub type Odd2<T> = Odd<T,U2>;
///A 3-dimensional odd value
pub type Odd3<T> = Odd<T,U3>;
///A 4-dimensional odd value
pub type Odd4<T> = Odd<T,U4>;
///A 5-dimensional odd value
pub type Odd5<T> = Odd<T,U5>;
///A 6-dimensional odd value
pub type Odd6<T> = Odd<T,U6>;
///An odd value with dynamic dimension
pub type OddD<T> = Odd<T,Dynamic>;

///A 0-dimensional multivector
pub type Multivector0<T> = Multivector<T,U0>;
///A 1-dimensional multivector
pub type Multivector1<T> = Multivector<T,U1>;
///A 2-dimensional multivector
pub type Multivector2<T> = Multivector<T,U2>;
///A 3-dimensional multivector
pub type Multivector3<T> = Multivector<T,U3>;
///A 4-dimensional multivector
pub type Multivector4<T> = Multivector<T,U4>;
///A 5-dimensional multivector
pub type Multivector5<T> = Multivector<T,U5>;
///A 6-dimensional multivector
pub type Multivector6<T> = Multivector<T,U6>;
///A multivector with dynamic dimension
pub type MultivectorD<T> = Multivector<T,Dynamic>;

///A scalar in N-dimensions
pub type Scalar<T,N> = Blade<T,N,U0>;
///A scalar in 0-dimensions
pub type Scalar0<T> = Scalar<T,U0>;
///A scalar in 1-dimension
pub type Scalar1<T> = Scalar<T,U1>;
///A scalar in 2-dimensions
pub type Scalar2<T> = Scalar<T,U2>;
///A scalar in 3-dimensions
pub type Scalar3<T> = Scalar<T,U3>;
///A scalar in 4-dimensions
pub type Scalar4<T> = Scalar<T,U4>;
///A scalar in 5-dimensions
pub type Scalar5<T> = Scalar<T,U5>;
///A scalar in 6-dimensions
pub type Scalar6<T> = Scalar<T,U6>;
///A scalar in a dynamic number of dimensions
pub type ScalarD<T> = Scalar<T,Dynamic>;

///An N-dimensional vector
pub type VecN<T,N> = Blade<T,N,U1>;
///A 1-dimensional vector
pub type Vec1<T> = VecN<T,U1>;
///A 2-dimensional vector
pub type Vec2<T> = VecN<T,U2>;
///A 3-dimensional vector
pub type Vec3<T> = VecN<T,U3>;
///A 4-dimensional vector
pub type Vec4<T> = VecN<T,U4>;
///A 5-dimensional vector
pub type Vec5<T> = VecN<T,U5>;
///A 6-dimensional vector
pub type Vec6<T> = VecN<T,U6>;
///A vector with dynamic dimension
pub type VecD<T> = VecN<T,Dynamic>;

///An N-dimensional bivector
pub type BiVecN<T,N> = Blade<T,N,U2>;
///A 2-dimensional bivector
pub type BiVec2<T> = BiVecN<T,U2>;
///A 3-dimensional bivector
pub type BiVec3<T> = BiVecN<T,U3>;
///A 4-dimensional bivector
pub type BiVec4<T> = BiVecN<T,U4>;
///A 5-dimensional bivector
pub type BiVec5<T> = BiVecN<T,U5>;
///A 6-dimensional bivector
pub type BiVec6<T> = BiVecN<T,U6>;
///A bivector with dynamic dimension
pub type BiVecD<T> = BiVecN<T,Dynamic>;

///An N-dimensional trivector
pub type TriVecN<T,N> = Blade<T,N,U3>;
///A 3-dimensional trivector
pub type TriVec3<T> = TriVecN<T,U3>;
///A 4-dimensional trivector
pub type TriVec4<T> = TriVecN<T,U4>;
///A 5-dimensional trivector
pub type TriVec5<T> = TriVecN<T,U5>;
///A 6-dimensional trivector
pub type TriVec6<T> = TriVecN<T,U6>;
///A trivector with dynamic dimension
pub type TriVecD<T> = TriVecN<T,Dynamic>;

///An N-dimensional quadvector
pub type QuadVecN<T,N> = Blade<T,N,U4>;
///A 4-dimensional quadvector
pub type QuadVec4<T> = QuadVecN<T,U4>;
///A 5-dimensional quadvector
pub type QuadVec5<T> = QuadVecN<T,U5>;
///A 6-dimensional quadvector
pub type QuadVec6<T> = QuadVecN<T,U6>;
///A quadvector with dynamic dimension
pub type QuadVecD<T> = QuadVecN<T,Dynamic>;

///An N-dimensional pentavector
pub type PentVecN<T,N> = Blade<T,N,U5>;
///A 5-dimensional pentavector
pub type PentVec5<T> = PentVecN<T,U5>;
///A 6-dimensional pentavector
pub type PentVec6<T> = PentVecN<T,U6>;
///A pentavector with dynamic dimension
pub type PentVecD<T> = PentVecN<T,Dynamic>;

///An N-dimensional hexavector
pub type HexVecN<T,N> = Blade<T,N,U6>;
///A 6-dimensional hexavector
pub type HexVec6<T> = HexVecN<T,U6>;
///A hexavector with dynamic dimension
pub type HexVecD<T> = HexVecN<T,Dynamic>;


pub type DualBlade<T,N,G> = Blade<T,N,DimDiff<N,G>>;

///
/// An N-dimensional psuedoscalar
///
/// A psuedoscalar is a blade in dimension `N` that has grade `N`. Blades of this type have only
/// one component and act the same as scalars in multiplication operations (up to a
/// possible extra minus sign).
///
/// Psuedoscalars are useful as they can be used to compute the dual of a blade and represent
/// (hyper)volume elements in N-dimensions.
///
pub type PsuedoScalar<T,N> = Blade<T,N,N>;

///
/// An N-dimensional psuedovector
///
/// A psuedovector is a blade in dimension `N` that has grade `N-1`. Blades of this type have N
/// components and act the same as vectors in multiplication operations
// (up to a possible extra minus sign).
///
/// Psuedovectors are useful as they represent hyperplanes in N-dimensions and are the dual of
/// vectors.
///
pub type PsuedoVecN<T,N> = Blade<T,N,DimDiff<N,U1>>;
