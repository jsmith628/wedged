
A robust and generalized library for Geometric Algebra in Rust.

# What is Geometric Algebra?

Geometric algebra is an extension of linear algebra where vectors are extended
with a multiplication operation called the _geometric product_, which
produces new kinds of operations and vector-like objects that are useful in
simplifying and generalizing a number of tricky systems in math and physics.

For instance:
- In physics, using "bivectors" geometric algebra provides a consistent and
  clean way of representing angular velocities in *any* dimension, which
  normally isn't possible in the standard system of angles and vectors.
- Geometric algebra unifies the rotational actions of Complex
  numbers and Quaternions into a single object called a Rotor that works in all
  dimensions.
- Using "unit blades", geometric algebra gives a compact and efficient way to
  represent vector and affine spaces that's easier to work with
  than sets of basis vectors.

For more information and an in depth explanation, I _highly_ recommend
[_Geometric Algebra for Computer Science_][1] by Leo Durst, Daniel Frontijne, and
Stephann Mann. A lot of inspiration for this library comes from that book, and
the concepts are explained in a way that's easy to follow and visual without
falling *too* deep into overly abstract math.

# Usage

This crate is split up into a number of modules each representing a different
interpretation of the underlying algebra:
 - `algebra` contains the most raw form of Geometric algebra defined purely
   algebraically. This is primarily used as the core all the other systems are
   built upon, but it is useful as well for various physical quantities (like
   position and angular velocity) and abstract mathematical objects
 - `subspace` interprets the structs in `algebra` as weighted vector spaces and
   orthogonal transformation (like rotations and reflections) in ℝ<sup>n</sup>
 - `homogenous` (planned) interprets the structs in `algebra` as affine spaces
   and their operations in ℝ<sup>n-1</sup> using homogeneous coordinates

Additionally, the module `wedged::base` contains the core components common
to all subsystems.

## Nomenclature and Conventions

Naming in geometric algebra can vary slightly across authors, so the particular
conventions have been chosen:
- in `wedged`, a `SimpleBlade` refers to an object constructed from the
 wedge product of vectors whereas a `Blade` refers to _any_ object of a
 particular grade
- a `Rotor` is used exclusively for objects with unit norm that encode rotations
  whereas `Even` is used for a general object from the even subalgebra
- `Multivector`s refer to a general element in the algebra
- The operators `*`/`Mul`, `^`/`BitXor`, and `%`/`Rem` are used for the geometric,
 wedge, and generalized dot products respectively

Additionally, most structs in this crate support indexing where each component
is ordered according to a particular basis convention chosen for this crate.
See the docs on `BasisBlade` For more information.

## Generic programming

In order to generalize code for different scalar types and dimensions,
`wedged` makes heavy use of generics. The system is based upon the
system in [`nalgebra`][2], and, to increase interoperability, reuses a lot of its
components.

The system is designed such that a number of different levels of abstraction
are possible:

### No Generics

```rust

use wedged::algebra::*;

let v1 = Vec3::new(1.0, 0.0, 0.0);
let v2 = Vec3::new(0.0, 1.0, 0.0);
let plane = v1 ^ v2;
let cross = plane.dual();

assert_eq!(plane, BiVec3::new(0.0,0.0,1.0));
assert_eq!(cross, Vec3::new(0.0,0.0,1.0));

```

When not using generics, things act much like you would expect from a vector
library.

### Generic Scalar

```rust

use wedged::algebra::*;
use wedged::base::ops::*;

fn midpoint<T:Clone+ClosedAdd+ClosedDiv+One>(v1:Vec3<T>, v2:Vec3<T>) -> Vec3<T> {
  let two = T::one() + T::one();
  (v1 + v2) / two
}

fn cross<T:RefRing>(v1:Vec3<T>, v2:Vec3<T>) -> Vec3<T> {
  (v1 ^ v2).dual()
}

let v1 = Vec3::new(1.0, 0.0, 0.0);
let v2 = Vec3::new(0.0, 1.0, 0.0);
assert_eq!(cross(v1,v2), Vec3::new(0.0,0.0,1.0));
assert_eq!(midpoint(v1,v2), Vec3::new(0.5,0.5,0.0));

let v1 = Vec3::new(1.0f32, 0.0, 0.0);
let v2 = Vec3::new(0.0f32, 1.0, 0.0);
assert_eq!(cross(v1,v2), Vec3::new(0.0f32,0.0,1.0));
assert_eq!(midpoint(v1,v2), Vec3::new(0.5f32,0.5,0.0));

```

For generic scalars, `wedged` structs implement traits and functions based on
what their scalars implement. For instance:
 - Structural traits like `Index`, `AsRef<[T]>`, and `Borrow<[T]>` are always
   implemented
 - Basic traits like `Clone`, `fmt` traits, `PartialEq`, `Eq`, `Hash`, and `Default`
   are all implemented if the scalar implements them
 - `Copy` is implemented if the scalar is `Copy` the struct isn't a `Dynamic`
   dimension
 - Additive operations like `Add`, `Sub`, and `Neg` as well as scalar operations
   like `Mul` and `Div`. are implemented if the scalar has them. The assign
   variants and operations between references are implemented as well if the
   scalars implement them.
 - Traits for the geometric (`Mul`), wedge (`BitXor`), and dot (`Rem`) products
   are implemented if the scalar has addition, subtraction, negation, zero and
   multiplication between references
 - anything involving a norm, constructing a rotation, etc, requires
   `nalgebra::real_field`
 - `Div` _usually_ has the same requirements as `Mul`, but is only implemented
   on a few specific structs (like `Rotor` and `Versor`)

In order to make managing these requirements easier, a number of trait aliases
are included in `wedged::base::ops` that combine common groupings of operations
together

### Generic Dimension

```rust

use wedged::base::*;
use wedged::algebra::*;

fn point_velocity<T,N:Dim>(p:VecN<T,N>, angular_vel: BiVecN<T,N>) -> VecN<T,N> where
  T:AllocBlade<N,U1>+AllocBlade<N,U2>+RefRing
{
  p % angular_vel
}

let p = Vec2::new(2.0,0.0);
let av = BiVec2::new(3.0);
assert_eq!(point_velocity(p, av), Vec2::new(0.0,6.0));

let p = Vec3::new(0.0,2.0,0.0);
let av = BiVec3::new(3.0,0.0,0.0);
assert_eq!(point_velocity(p, av), Vec3::new(0.0,0.0,6.0));

```

For a generic dimension, for every `wedged` struct
used in the function or trait, the scalar must have the corresponding `Alloc*`
trait bound for that struct. These are all included in `wedged::base::alloc`,
and there is one for each subset of the geometric algebra.

For example, for a scalar `T` and dimension `N`, using a `VecN` requires `T:AllocBlade<N,U1>` bound, using an `Even` needs a `T:AllocEven<N>` bound, etc.

Finally, even if a non-generic scalar is used, these are still required inside a
where clause on the function or trait.

### Generic Dimension and Grade

```

use wedged::base::*;
use wedged::algebra::*;

fn project<T,N:Dim,G:Dim>(v:VecN<T,N>, b:Blade<T,N,G>) -> VecN<T,N> where
  U1: DimSymSub<G>,
  DimSymDiff<U1,G>: DimSymSub<G,Output=U1>,
  T:AllocBlade<N,U1> + AllocBlade<N,G> + AllocBlade<N,DimSymDiff<U1,G>> + RefDivRing
{
  let l = b.norm_sqrd();
  (v % &b) % b.reverse()/l
}

let v = Vec3::new(1.0, 2.0, 0.0);
let line = Vec3::new(0.0, 1.0, 0.0);
let plane = BiVec3::new(0.0, 1.0, 0.0);

assert_eq!(project(v,line), Vec3::new(0.0, 2.0, 0.0));
assert_eq!(project(v,plane), Vec3::new(1.0, 0.0, 0.0));

```

Using a generic grade follows nearly the same rules as for generic dimensions
but with an added generic for the grade. However, with grade altering operations
like the wedge or dot products are used, additional bounds are required to allow
the compiler to add or subtract the grades of the two blades.

For instance:
 - The wedge `^` product requires `G1: DimAdd<G2>`
 - The dot `%` product requires `G1: DimSymSub<G2>`



[1]: https://geometricalgebra.org/
[2]: https://www.nalgebra.org/
