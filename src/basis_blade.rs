
use num_traits::{One, Inv};
use std::ops::{Neg, Mul, MulAssign, Div, DivAssign};
use std::fmt::{Formatter, Debug, Display, Binary, Result as FmtResult};

//So we can maybe change it later though there really is no reason it needs any more bits than this
type Bits = i32;

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct BasisBlade {
    bits: Bits
}

impl BasisBlade {

    pub const MAX_DIM: usize = Bits::MAX.count_ones() as usize;

    ///
    /// Clears the sign bit
    ///
    /// This isn't `pub` since there is non-arbitry choice for when a basis blade is negative
    /// or positive. This is simply an internal function relative the internal representation.
    ///
    pub(crate) const fn abs(self) -> BasisBlade {
        //mask out the first bit
        BasisBlade { bits: self.bits & Bits::MAX }
    }

    ///
    /// Gets the sign bit as either `BasisBlade::one()` or `-BasisBlade::one()`
    ///
    /// This isn't `pub` since there is non-arbitry choice for when a basis blade is negative
    /// or positive. This is simply an internal function relative the internal representation.
    ///
    #[allow(dead_code)]
    pub(crate) const fn sign(self) -> BasisBlade {
        //get just the first bit
        BasisBlade { bits: self.bits & Bits::MIN }
    }

    ///
    /// Returns the nth basis vector
    ///
    /// Panics if n is greater than the maximum dimension
    ///
    pub fn basis_vector(n: usize) -> BasisBlade {
        if n >= Self::MAX_DIM {
            panic!("Only Vectors up to dimension {} are currently supported", Self::MAX_DIM )
        }
        BasisBlade { bits: 1 << n }
    }

    ///
    /// Returns the nth basis vector
    ///
    /// Returns `BasisBlade::one()` if n is greater than the maximum dimension
    ///
    pub const fn const_basic_vector(n: usize) -> BasisBlade {
        BasisBlade { bits: 1 << n }.abs()
    }

    ///
    /// Computes the minimum dimension this `BasisBlade` is contained in
    ///
    /// # Examples
    ///```
    /// # use galgebra::basis_blade::*;
    /// # use num_traits::One;
    ///
    /// let e = BasisBlade::one();
    /// let e1 = BasisBlade::basis_vector(0);
    /// let e2 = BasisBlade::basis_vector(1);
    /// let e3 = BasisBlade::basis_vector(2);
    /// let e12 = e1*e2;
    /// let e13 = e1*e3;
    /// let e23 = e2*e3;
    /// let e123 = e1*e2*e3;
    ///
    /// assert_eq!(e.dim(), 0);
    /// assert_eq!(e1.dim(), 1);
    /// assert_eq!(e2.dim(), 2);
    /// assert_eq!(e3.dim(), 3);
    /// assert_eq!(e12.dim(), 2);
    /// assert_eq!(e13.dim(), 3);
    /// assert_eq!(e23.dim(), 3);
    /// assert_eq!(e123.dim(), 3);
    /// assert_eq!((-e123).dim(), 3);
    ///
    ///```
    ///
    pub const fn dim(&self) -> usize {
        (Bits::BITS - self.abs().bits.leading_zeros()) as usize
    }

    ///
    /// Computes the grade of this `BasisBlade`
    ///
    /// # Examples
    ///```
    /// # use galgebra::basis_blade::*;
    /// # use num_traits::One;
    ///
    /// let e = BasisBlade::one();
    /// let e1 = BasisBlade::basis_vector(0);
    /// let e2 = BasisBlade::basis_vector(1);
    /// let e3 = BasisBlade::basis_vector(2);
    /// let e12 = e1*e2;
    /// let e13 = e1*e3;
    /// let e23 = e2*e3;
    /// let e123 = e1*e2*e3;
    ///
    /// assert_eq!(e.grade(), 0);
    /// assert_eq!(e1.grade(), 1);
    /// assert_eq!(e2.grade(), 1);
    /// assert_eq!(e3.grade(), 1);
    /// assert_eq!(e12.grade(), 2);
    /// assert_eq!(e13.grade(), 2);
    /// assert_eq!(e23.grade(), 2);
    /// assert_eq!(e123.grade(), 3);
    /// assert_eq!((-e123).grade(), 3);
    ///
    ///```
    ///
    pub const fn grade(&self) -> usize {
        self.abs().bits.count_ones() as usize
    }

}

impl Binary for BasisBlade {
    fn fmt(&self, f: &mut Formatter) -> FmtResult {
        write!(f, "{:b}", self.bits)
    }
}

impl One for BasisBlade {
    //1 is just the empty product. ie when bits==0
    fn one() -> Self { BasisBlade { bits: 0 } }
    fn is_one(&self) -> bool { self.bits == 0 }
}

impl Neg for BasisBlade {
    type Output = Self;
    fn neg(self) -> Self {
        //flip the first bit
        BasisBlade { bits: self.bits ^ Bits::MIN }
    }
}

impl Inv for BasisBlade {
    type Output = Self;
    fn inv(self) -> Self {
        //to invert, we need to reverse the order of the basic vectors:
        //- To do this, we must pass the `i`th vector in the mul through the `i-1` vectors before it
        //  giving `i-1` swaps for each of the g vectors.
        //- Summing this all up, we get `0 + 1 + .. (g-1) = g*(g-1)/2` total swaps
        //- Now, this value is only even iff `4 | g*(g-1)`
        //- but this can only happen if either `4|g` or `4|(g-1)` as 2 cannot divide both `g` and
        //  `g-1` at the same time
        //- Therefore, to invert, we negate iff g == 2,3 mod 4

        //get the grade
        let g = self.grade() as Bits;

        //test if the grade is 2 or 3 mod 4 by masking out the 2nd bit
        //and then shifting that bit to the leading position
        let sign = (g & 0b10) << (Self::MAX_DIM-1);

        //multiply self by sign
        BasisBlade { bits: self.bits ^ sign }

    }
}

impl Mul for BasisBlade {
    type Output = Self;
    fn mul(self, rhs: Self) -> Self {

        //we only have to abs() self since it will mask out the sign of rhs
        let mut a = self.abs().bits;
        let b = rhs.bits;

        //compute the sign of the result by computing the number of swaps
        //required to align all the basis vectors
        a >>= 1;
        let mut swaps = 0;
        while a!=0 {
            swaps += (a&b).count_ones() as Bits;
            a >>= 1
        }

        //if swaps is even, this is 0, if it is odd, it is Bits::MIN
        let sign = (swaps & 1) << Self::MAX_DIM;

        //xor everything together
        //self.bits ^ rhs.bits selects out all basis vectors not in common
        //^ sign flips the sign according to the swaps we had to do
        BasisBlade { bits: self.bits ^ rhs.bits ^ sign }

    }
}

impl Div for BasisBlade {
    type Output = Self;
    fn div(self, rhs: Self) -> Self { self * rhs.inv() }
}

macro_rules! impl_bin_op {
    ($Op:ident.$op:ident() $Assign:ident.$assign:ident()) => {
        impl<'a> $Op<&'a BasisBlade> for BasisBlade {
            type Output = BasisBlade;
            fn $op(self, rhs: &'a BasisBlade) -> BasisBlade { self.$op(*rhs) }
        }

        impl<'a> $Op<BasisBlade> for &'a BasisBlade {
            type Output = BasisBlade;
            fn $op(self, rhs: BasisBlade) -> BasisBlade { (*self).$op(rhs) }
        }

        impl<'a,'b> $Op<&'b BasisBlade> for &'a BasisBlade {
            type Output = BasisBlade;
            fn $op(self, rhs: &'b BasisBlade) -> BasisBlade { (*self).$op(*rhs) }
        }

        impl $Assign for BasisBlade {
            fn $assign(&mut self, rhs: Self) { *self = self.$op(rhs) }
        }
    }
}

impl_bin_op!(Mul.mul() MulAssign.mul_assign());
impl_bin_op!(Div.div() DivAssign.div_assign());

#[cfg(test)]
#[allow(non_upper_case_globals)]
mod tests {

    use super::*;

    const e: BasisBlade = BasisBlade { bits: 0 };

    const e1: BasisBlade = BasisBlade::const_basic_vector(0);
    const e2: BasisBlade = BasisBlade::const_basic_vector(1);
    const e3: BasisBlade = BasisBlade::const_basic_vector(2);
    const e4: BasisBlade = BasisBlade::const_basic_vector(3);

    const e12: BasisBlade = BasisBlade { bits: 0b0011 };
    const e13: BasisBlade = BasisBlade { bits: 0b0101 };
    const e14: BasisBlade = BasisBlade { bits: 0b1001 };
    const e23: BasisBlade = BasisBlade { bits: 0b0110 };
    const e24: BasisBlade = BasisBlade { bits: 0b1010 };
    const e34: BasisBlade = BasisBlade { bits: 0b1100 };

    const e123: BasisBlade = BasisBlade { bits: 0b0111 };
    const e124: BasisBlade = BasisBlade { bits: 0b1011 };
    const e134: BasisBlade = BasisBlade { bits: 0b1101 };
    const e234: BasisBlade = BasisBlade { bits: 0b1110 };

    const e1234: BasisBlade = BasisBlade { bits: 0b1111 };

    #[test]
    fn abs() {

        macro_rules! test_abs {
            ($($e:ident)*) => {
                $(
                    assert_eq!($e.abs(), $e);
                    assert_eq!((-$e).abs(), $e);
                )*
            }
        }

        test_abs!(e e1 e2 e3 e4 e12 e13 e14 e23 e24 e34 e123 e124 e134 e234 e1234);
    }

    #[test]
    fn sign() {

        macro_rules! test_sign {
            ($($e:ident)*) => {
                $(
                    assert_eq!($e.sign(), e);
                    assert_eq!((-$e).sign(), -e);
                )*
            }
        }

        test_sign!(e e1 e2 e3 e4 e12 e13 e14 e23 e24 e34 e123 e124 e134 e234 e1234);
    }

    macro_rules! test_mul {
        ($b1:ident*$b2:ident == $b3:expr; $commutative:literal) => {

            assert_eq!( $b1 * $b2,  $b3);
            assert_eq!(-$b1 * $b2, -$b3);
            assert_eq!( $b1 *-$b2, -$b3);
            assert_eq!(-$b1 *-$b2,  $b3);

            if $commutative {
                assert_eq!( $b2 * $b1,  $b3);
                assert_eq!(-$b2 * $b1, -$b3);
                assert_eq!( $b2 *-$b1, -$b3);
                assert_eq!(-$b2 *-$b1,  $b3);
            } else {
                assert_eq!( $b2 * $b1, -$b3);
                assert_eq!(-$b2 * $b1,  $b3);
                assert_eq!( $b2 *-$b1,  $b3);
                assert_eq!(-$b2 *-$b1, -$b3);
            }

        }
    }

    #[test]
    fn mul() {

        test_mul!(e1*e1 == e; true);
        test_mul!(e2*e2 == e; true);
        test_mul!(e3*e3 == e; true);

        test_mul!(e1*e2 == e12; false);
        test_mul!(e1*e3 == e13; false);
        test_mul!(e2*e3 == e23; false);

        test_mul!(e13*e12 == e23; false);
        test_mul!(e12*e23 == e13; false);
        test_mul!(e23*e13 == e12; false);

        test_mul!(e1*e12 == e2; false);
        test_mul!(e12*e2 == e1; false);
        test_mul!(e1*e13 == e3; false);
        test_mul!(e13*e3 == e1; false);
        test_mul!(e2*e23 == e3; false);
        test_mul!(e23*e3 == e2; false);

        test_mul!(e12*e3 ==  e123; true);
        test_mul!(e13*e2 == -e123; true);
        test_mul!(e1*e23 ==  e123; true);

        test_mul!(e1*e123 ==  e23; true);
        test_mul!(e2*e123 == -e13; true);
        test_mul!(e3*e123 ==  e12; true);

        test_mul!(e12*e123 == -e3; true);
        test_mul!(e13*e123 ==  e2; true);
        test_mul!(e23*e123 == -e1; true);

        assert_eq!(e1*e2*e3,  e123);
        assert_eq!(e2*e1*e3, -e123);
        assert_eq!(e2*e3*e1,  e123);
        assert_eq!(e3*e2*e1, -e123);
        assert_eq!(e3*e1*e2,  e123);
        assert_eq!(e1*e3*e2, -e123);

    }

    #[test]
    fn one() {

        let one = BasisBlade::one();

        macro_rules! test_one {
            ($($e:ident)*) => {
                $(test_mul!(e*$e == $e; true);)*
            }
        }

        test_one!(e e1 e2 e3 e4 e12 e13 e14 e23 e24 e34 e123 e124 e134 e234 e1234);

    }

    #[test]
    fn inv() {
        macro_rules! test_inv {
            ($($e:ident)*) => {
                $(
                    assert_eq!(
                        $e.inv(),
                        {
                            let g = $e.grade();
                            if g==0 || g*(g-1)/2 % 2 == 0 { $e } else { -$e }
                        }
                    );
                )*
            }
        }

        test_inv!(e e1 e2 e3 e4 e12 e13 e14 e23 e24 e34 e123 e124 e134 e234 e1234);
    }

    #[test]
    fn div() {

        macro_rules! test_div {
            ($($e:ident)*) => {
                $(assert_eq!($e/$e, e);)*
            }
        }

        test_div!(e e1 e2 e3 e4 e12 e13 e14 e23 e24 e34 e123 e124 e134 e234 e1234);

    }

}
