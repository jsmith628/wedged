
# `galgebra`

A robust and generalized library for Geometric and Clifford Algebras in Rust.

## What even is Geometric Algebra?

In short, it is an extension of linear algebra where we give vectors the ability
to be multiplied together using a special operation called the _Geometric Product_,
producing various new objects and operations that are useful to generalize and
simplify a number of things in Linear Algebra and Physics that are normally
unruly to deal with.

For example:
- In physics, Geometric algebra provides a consistent and general way of
  representing angular velocities in *any* dimension by using a Bivector instead
  of the normal inconsistent system of an angle in 2D, a vector in 3D, and not
  generalizing to higher dimensions.
- Geometric algebra generalizes and unifies the rotational actions of Complex
  numbers and Quaternions into a single object called a Rotor that works in all
  dimensions using the same mode of action.

For more information and an in depth explanation, I _highly_ recommend
[_Geometric Algebra for Computer Science_][1] by Leo Durst, Daniel Frontijne, and
Stephann Mann. A lot of inspiration for this library comes from that book, and
the concepts are explained in a way that's easy to follow without falling too
deep into overly abstract math.

## Organization of this crate

This crate is split up into a number of modules each representing a different
interpretation and use-case of the underlying algebra:
 - `algebra` contains the most raw form of Geometric algebra defined purely
   algebraically. This is primarily used as the core all the other systems are
   built upon, but it is useful as well for various physical quantities (like
   position and angular velocity) and abstract mathematical objects
 - `subspace` interprets the structs in `algebra` as weighted vector spaces and
   their operations (like rotations and reflections) in ℝ<sup>n</sup>
 - (planned) `vector_space` interprets the structs in `algebra` as affine spaces
   and their operations in ℝ<sup>n-1</sup> using homogeneous coordinates


[1]: https://geometricalgebra.org/
[2]: https://www.nalgebra.org/
