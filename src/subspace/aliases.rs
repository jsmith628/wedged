
use super::*;


///An N-dimensional simple blade with a dynamic grade
pub type SimpleBladeN<T,N> = SimpleBlade<T,N,Dynamic>;
///A 0-dimensional simple blade with a dynamic grade
pub type SimpleBlade0<T> = SimpleBlade<T,U0,Dynamic>;
///A 1-dimensional simple blade with a dynamic grade
pub type SimpleBlade1<T> = SimpleBlade<T,U1,Dynamic>;
///A 2-dimensional simple blade with a dynamic grade
pub type SimpleBlade2<T> = SimpleBlade<T,U2,Dynamic>;
///A 3-dimensional simple blade with a dynamic grade
pub type SimpleBlade3<T> = SimpleBlade<T,U3,Dynamic>;
///A 4-dimensional simple blade with a dynamic grade
pub type SimpleBlade4<T> = SimpleBlade<T,U4,Dynamic>;
///A 5-dimensional simple blade with a dynamic grade
pub type SimpleBlade5<T> = SimpleBlade<T,U5,Dynamic>;
///A 6-dimensional simple blade with a dynamic grade
pub type SimpleBlade6<T> = SimpleBlade<T,U6,Dynamic>;
///A simple blade with a dynamic dimension and grade
pub type SimpleBladeD<T> = SimpleBlade<T,Dynamic,Dynamic>;

///An N-dimensional unit blade with a dynamic grade
pub type UnitBladeN<T,N> = UnitBlade<T,N,Dynamic>;
///A 0-dimensional unit blade with a dynamic grade
pub type UnitBlade0<T> = UnitBlade<T,U0,Dynamic>;
///A 1-dimensional unit blade with a dynamic grade
pub type UnitBlade1<T> = UnitBlade<T,U1,Dynamic>;
///A 2-dimensional unit blade with a dynamic grade
pub type UnitBlade2<T> = UnitBlade<T,U2,Dynamic>;
///A 3-dimensional unit blade with a dynamic grade
pub type UnitBlade3<T> = UnitBlade<T,U3,Dynamic>;
///A 4-dimensional unit blade with a dynamic grade
pub type UnitBlade4<T> = UnitBlade<T,U4,Dynamic>;
///A 5-dimensional unit blade with a dynamic grade
pub type UnitBlade5<T> = UnitBlade<T,U5,Dynamic>;
///A 6-dimensional unit blade with a dynamic grade
pub type UnitBlade6<T> = UnitBlade<T,U6,Dynamic>;
///A unit blade with a dynamic dimension and grade
pub type UnitBladeD<T> = UnitBlade<T,Dynamic,Dynamic>;

///A 0-dimensional rotor
pub type Rotor0<T> = Rotor<T,U0>;
///A 1-dimensional rotor
pub type Rotor1<T> = Rotor<T,U1>;
///A 2-dimensional rotor
pub type Rotor2<T> = Rotor<T,U2>;
///A 3-dimensional rotor
pub type Rotor3<T> = Rotor<T,U3>;
///A 4-dimensional rotor
pub type Rotor4<T> = Rotor<T,U4>;
///A 5-dimensional rotor
pub type Rotor5<T> = Rotor<T,U5>;
///A 6-dimensional rotor
pub type Rotor6<T> = Rotor<T,U6>;
///A rotor with dynamic dimension
pub type RotorD<T> = Rotor<T,Dynamic>;

///A 0-dimensional reflector
pub type Reflector0<T> = Reflector<T,U0>;
///A 1-dimensional reflector
pub type Reflector1<T> = Reflector<T,U1>;
///A 2-dimensional reflector
pub type Reflector2<T> = Reflector<T,U2>;
///A 3-dimensional reflector
pub type Reflector3<T> = Reflector<T,U3>;
///A 4-dimensional reflector
pub type Reflector4<T> = Reflector<T,U4>;
///A 5-dimensional reflector
pub type Reflector5<T> = Reflector<T,U5>;
///A 6-dimensional reflector
pub type Reflector6<T> = Reflector<T,U6>;
///An reflector with dynamic dimension
pub type ReflectorD<T> = Reflector<T,Dynamic>;

///A 0-dimensional versor
pub type Versor0<T> = Versor<T,U0>;
///A 1-dimensional versor
pub type Versor1<T> = Versor<T,U1>;
///A 2-dimensional versor
pub type Versor2<T> = Versor<T,U2>;
///A 3-dimensional versor
pub type Versor3<T> = Versor<T,U3>;
///A 4-dimensional versor
pub type Versor4<T> = Versor<T,U4>;
///A 5-dimensional versor
pub type Versor5<T> = Versor<T,U5>;
///A 6-dimensional versor
pub type Versor6<T> = Versor<T,U6>;
///An versor with dynamic dimension
pub type VersorD<T> = Versor<T,Dynamic>;

///A scalar in N-dimensions
pub type SimpleScalar<T,N> = SimpleBlade<T,N,U0>;
///A scalar in 0-dimensions
pub type SimpleScalar0<T> = SimpleScalar<T,U0>;
///A scalar in 1-dimension
pub type SimpleScalar1<T> = SimpleScalar<T,U1>;
///A scalar in 2-dimensions
pub type SimpleScalar2<T> = SimpleScalar<T,U2>;
///A scalar in 3-dimensions
pub type SimpleScalar3<T> = SimpleScalar<T,U3>;
///A scalar in 4-dimensions
pub type SimpleScalar4<T> = SimpleScalar<T,U4>;
///A scalar in 5-dimensions
pub type SimpleScalar5<T> = SimpleScalar<T,U5>;
///A scalar in 6-dimensions
pub type SimpleScalar6<T> = SimpleScalar<T,U6>;
///A scalar in a dynamic number of dimensions
pub type SimpleScalarD<T> = SimpleScalar<T,Dynamic>;

///A scalar in N-dimensions
pub type UnitScalar<T,N> = UnitBlade<T,N,U0>;
///A scalar in 0-dimensions
pub type UnitScalar0<T> = UnitScalar<T,U0>;
///A scalar in 1-dimension
pub type UnitScalar1<T> = UnitScalar<T,U1>;
///A scalar in 2-dimensions
pub type UnitScalar2<T> = UnitScalar<T,U2>;
///A scalar in 3-dimensions
pub type UnitScalar3<T> = UnitScalar<T,U3>;
///A scalar in 4-dimensions
pub type UnitScalar4<T> = UnitScalar<T,U4>;
///A scalar in 5-dimensions
pub type UnitScalar5<T> = UnitScalar<T,U5>;
///A scalar in 6-dimensions
pub type UnitScalar6<T> = UnitScalar<T,U6>;
///A scalar in a dynamic number of dimensions
pub type UnitScalarD<T> = UnitScalar<T,Dynamic>;

///An N-dimensional vector
pub type SimpleVecN<T,N> = SimpleBlade<T,N,U1>;
///A 1-dimensional vector
pub type SimpleVec1<T> = SimpleVecN<T,U1>;
///A 2-dimensional vector
pub type SimpleVec2<T> = SimpleVecN<T,U2>;
///A 3-dimensional vector
pub type SimpleVec3<T> = SimpleVecN<T,U3>;
///A 4-dimensional vector
pub type SimpleVec4<T> = SimpleVecN<T,U4>;
///A 5-dimensional vector
pub type SimpleVec5<T> = SimpleVecN<T,U5>;
///A 6-dimensional vector
pub type SimpleVec6<T> = SimpleVecN<T,U6>;
///A vector with dynamic dimension
pub type SimpleVecD<T> = SimpleVecN<T,Dynamic>;

///An N-dimensional unit vector
pub type UnitVecN<T,N> = UnitBlade<T,N,U1>;
///A 1-dimensional unit vector
pub type UnitVec1<T> = UnitVecN<T,U1>;
///A 2-dimensional unit vector
pub type UnitVec2<T> = UnitVecN<T,U2>;
///A 3-dimensional unit vector
pub type UnitVec3<T> = UnitVecN<T,U3>;
///A 4-dimensional unit vector
pub type UnitVec4<T> = UnitVecN<T,U4>;
///A 5-dimensional unit vector
pub type UnitVec5<T> = UnitVecN<T,U5>;
///A 6-dimensional unit vector
pub type UnitVec6<T> = UnitVecN<T,U6>;
///A unit vector with dynamic dimension
pub type UnitVecD<T> = UnitVecN<T,Dynamic>;

///An N-dimensional simple bivector
pub type SimpleBiVecN<T,N> = SimpleBlade<T,N,U2>;
///A 2-dimensional simple bivector
pub type SimpleBiVec2<T> = SimpleBiVecN<T,U2>;
///A 3-dimensional simple bivector
pub type SimpleBiVec3<T> = SimpleBiVecN<T,U3>;
///A 4-dimensional simple bivector
pub type SimpleBiVec4<T> = SimpleBiVecN<T,U4>;
///A 5-dimensional simple bivector
pub type SimpleBiVec5<T> = SimpleBiVecN<T,U5>;
///A 6-dimensional simple bivector
pub type SimpleBiVec6<T> = SimpleBiVecN<T,U6>;
///A simple bivector with dynamic dimension
pub type SimpleBiVecD<T> = SimpleBiVecN<T,Dynamic>;

///An N-dimensional unit bivector
pub type UnitBiVecN<T,N> = UnitBlade<T,N,U2>;
///A 2-dimensional unit bivector
pub type UnitBiVec2<T> = UnitBiVecN<T,U2>;
///A 3-dimensional unit bivector
pub type UnitBiVec3<T> = UnitBiVecN<T,U3>;
///A 4-dimensional unit bivector
pub type UnitBiVec4<T> = UnitBiVecN<T,U4>;
///A 5-dimensional unit bivector
pub type UnitBiVec5<T> = UnitBiVecN<T,U5>;
///A 6-dimensional unit bivector
pub type UnitBiVec6<T> = UnitBiVecN<T,U6>;
///A unit bivector with dynamic dimension
pub type UnitBiVecD<T> = UnitBiVecN<T,Dynamic>;

///An N-dimensional simple trivector
pub type SimpleTriVecN<T,N> = SimpleBlade<T,N,U3>;
///A 3-dimensional simple trivector
pub type SimpleTriVec3<T> = SimpleTriVecN<T,U3>;
///A 4-dimensional simple trivector
pub type SimpleTriVec4<T> = SimpleTriVecN<T,U4>;
///A 5-dimensional simple trivector
pub type SimpleTriVec5<T> = SimpleTriVecN<T,U5>;
///A 6-dimensional simple trivector
pub type SimpleTriVec6<T> = SimpleTriVecN<T,U6>;
///A simple trivector with dynamic dimension
pub type SimpleTriVecD<T> = SimpleTriVecN<T,Dynamic>;

///An N-dimensional unit trivector
pub type UnitTriVecN<T,N> = UnitBlade<T,N,U3>;
///A 3-dimensional unit trivector
pub type UnitTriVec3<T> = UnitTriVecN<T,U3>;
///A 4-dimensional unit trivector
pub type UnitTriVec4<T> = UnitTriVecN<T,U4>;
///A 5-dimensional unit trivector
pub type UnitTriVec5<T> = UnitTriVecN<T,U5>;
///A 6-dimensional unit trivector
pub type UnitTriVec6<T> = UnitTriVecN<T,U6>;
///A unit trivector with dynamic dimension
pub type UnitTriVecD<T> = UnitTriVecN<T,Dynamic>;

///An N-dimensional simple quadvector
pub type SimpleQuadVecN<T,N> = SimpleBlade<T,N,U4>;
///A 4-dimensional simple quadvector
pub type SimpleQuadVec4<T> = SimpleQuadVecN<T,U4>;
///A 5-dimensional simple quadvector
pub type SimpleQuadVec5<T> = SimpleQuadVecN<T,U5>;
///A 6-dimensional simple quadvector
pub type SimpleQuadVec6<T> = SimpleQuadVecN<T,U6>;
///A simple quadvector with dynamic dimension
pub type SimpleQuadVecD<T> = SimpleQuadVecN<T,Dynamic>;

///An N-dimensional unit quadvector
pub type UnitQuadVecN<T,N> = UnitBlade<T,N,U4>;
///A 4-dimensional unit quadvector
pub type UnitQuadVec4<T> = UnitQuadVecN<T,U4>;
///A 5-dimensional unit quadvector
pub type UnitQuadVec5<T> = UnitQuadVecN<T,U5>;
///A 6-dimensional unit quadvector
pub type UnitQuadVec6<T> = UnitQuadVecN<T,U6>;
///A unit quadvector with dynamic dimension
pub type UnitQuadVecD<T> = UnitQuadVecN<T,Dynamic>;

///An N-dimensional simple pentavector
pub type SimplePentVecN<T,N> = SimpleBlade<T,N,U5>;
///A 5-dimensional simple pentavector
pub type SimplePentVec5<T> = SimplePentVecN<T,U5>;
///A 6-dimensional simple pentavector
pub type SimplePentVec6<T> = SimplePentVecN<T,U6>;
///A simple pentavector with dynamic dimension
pub type SimplePentVecD<T> = SimplePentVecN<T,Dynamic>;

///An N-dimensional unit pentavector
pub type UnitPentVecN<T,N> = UnitBlade<T,N,U5>;
///A 5-dimensional unit pentavector
pub type UnitPentVec5<T> = UnitPentVecN<T,U5>;
///A 6-dimensional unit pentavector
pub type UnitPentVec6<T> = UnitPentVecN<T,U6>;
///A unit pentavector with dynamic dimension
pub type UnitPentVecD<T> = UnitPentVecN<T,Dynamic>;

///An N-dimensional simple hexavector
pub type SimpleHexVecN<T,N> = SimpleBlade<T,N,U6>;
///A 6-dimensional simple hexavector
pub type SimpleHexVec6<T> = SimpleHexVecN<T,U6>;
///A simple hexavector with dynamic dimension
pub type SimpleHexVecD<T> = SimpleHexVecN<T,Dynamic>;

///An N-dimensional unit hexavector
pub type UnitHexVecN<T,N> = UnitBlade<T,N,U6>;
///A 6-dimensional unit hexavector
pub type UnitHexVec6<T> = UnitHexVecN<T,U6>;
///A unit hexavector with dynamic dimension
pub type UnitHexVecD<T> = UnitHexVecN<T,Dynamic>;

pub type SimpleDualBlade<T,N,G> = SimpleBlade<T,N,DimDiff<N,G>>;
pub type UnitDualBlade<T,N,G> = UnitBlade<T,N,DimDiff<N,G>>;

/// An N-dimensional psuedoscalar
pub type SimplePsuedoScalar<T,N> = SimpleBlade<T,N,N>;

/// An N-dimensional unit psuedoscalar
pub type UnitPsuedoScalar<T,N> = UnitBlade<T,N,N>;

/// An N-dimensional psuedovector
pub type SimplePsuedoVecN<T,N> = SimpleBlade<T,N,DimNameDiff<N,U1>>;

/// An N-dimensional unit psuedovector
pub type UnitPsuedoVecN<T,N> = UnitBlade<T,N,DimNameDiff<N,U1>>;
