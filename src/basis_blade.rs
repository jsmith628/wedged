
use num_traits::{One, Inv};
use std::ops::{Neg, Mul, MulAssign, Div, DivAssign};
use std::fmt::{Formatter, Debug, Display, Binary, Result as FmtResult};

//So we can maybe change it later though there really is no reason it needs any more bits than this
type Bits = i32;

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct BasisBlade {
    bits: Bits
}

impl BasisBlade {

    pub const MAX_DIM: usize = Bits::MAX.count_ones() as usize;

    fn abs(self) -> BasisBlade {
        //mask out the first bit
        BasisBlade { bits: self.bits & Bits::MAX }
    }

    #[allow(dead_code)]
    fn sign(self) -> BasisBlade {
        //get just the first bit
        BasisBlade { bits: self.bits & Bits::MIN }
    }

    pub fn n_axis(n: usize) -> BasisBlade {
        if n >= Self::MAX_DIM {
            panic!("Only Vectors up to dimension {} are currently supported", Self::MAX_DIM )
        }
        BasisBlade { bits: 1 << n }
    }

    pub fn dim(&self) -> usize {
        (Bits::BITS - self.abs().bits.leading_zeros()) as usize
    }

    pub fn grade(&self) -> usize {
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
        let sign = swaps&1 << Self::MAX_DIM;

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
