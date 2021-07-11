
use num_traits::{One, Inv};
use std::ops::{Neg, Mul, MulAssign, Div, DivAssign};
use std::fmt::{Formatter, Debug, Display, Binary, Result as FmtResult, Alignment};

use super::binom;

//So we can maybe change it later though there really is no reason it needs any more bits than this
type Bits = i32;

#[repr(transparent)]
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct BasisBlade {
    bits: Bits
}

impl BasisBlade {

    ///The maximum number of dimensions supported
    pub const MAX_DIM: usize = (Bits::BITS - 1) as usize; //the bit width minus one for the sign

    ///The multiplicative identity
    pub const ONE: BasisBlade = BasisBlade { bits: 0 }; //1 is just the empty product (ie when bits==0)

    ///Negative one
    pub const NEG_ONE: BasisBlade = BasisBlade { bits: Bits::MIN }; //0 with the leading bit flipped

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
    pub(crate) const fn sign(self) -> BasisBlade {
        //get just the first bit
        BasisBlade { bits: self.bits & Bits::MIN }
    }

    pub(crate) const fn positive(self) -> bool {
        self.sign().bits == BasisBlade::ONE.bits
    }

    pub(crate) const fn negative(self) -> bool {
        self.sign().bits == BasisBlade::NEG_ONE.bits
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
    pub const fn const_basis_vector(n: usize) -> BasisBlade {
        BasisBlade { bits: 1 << n }.abs()
    }

    pub const fn basis_blade(n:usize, g:usize, i:usize) -> BasisBlade {

        //TODO: panics for invalid blades

        //invalid basis vectors
        if g>n || i>binom(n,g) { return Self::ONE; }

        //Rule #0: if grade==0, then the basis is just the identity
        if g==0 { return Self::ONE; }

        if n==2 && g==2 { return BasisBlade { bits: 0b11 }; }

        //rule #1: if grade==1, then the basis is e_i
        if g==1 { return Self::const_basis_vector(i); }

        if g <= n/2 {
            //the number of elements of this grade in the prev dimension
            let count_prev = binom(n-1,g);

            if i < count_prev {
                //Rule #2: if g<=n/2 and i<binom(n-1,g), then the basis is the same as in the previous dimension
                Self::basis_blade(n-1,g,i)
            } else {

                //Rule #4: for g<n/2, basis_blade(n,g,i) == basis_blade(n,n-g,i) / psuedoscalar(n)

                //From this, we can prove that psuedoscalar(n) = e_n * psuedoscalar(n-1) (for n>2)
                //as e_n = basis_blade(n,n-1,n-1) / psuedoscalar(n)
                //so 1 = e_n * basis_blade(n,n-1,n-1) / psuedoscalar(n)
                //   psuedoscalar(n) = e_n * basis_blade(n,n-1,n-1)
                //but since n>2, by Rule #3: basis_blade(n,n-1,n-1) = basis_blade(n-1,n-1,0), so therefore
                //   psuedoscalar(n) = e_n * psuedoscalar(n-1)

                //next, we use this as follows: for i > binom(n-1,g)
                //   basis_blade(n,g,i) == basis_blade(n,n-g,i) / psuedoscalar(n)
                //   basis_blade(n,g,i) == basis_blade(n,n-g,i) * psuedoscalar(n).inv()
                //   basis_blade(n,g,i) == basis_blade(n,n-g,i) * (e_n * psuedoscalar(n-1)).inv()
                //   basis_blade(n,g,i) == basis_blade(n,n-g,i) * psuedoscalar(n-1).inv() * e_n
                //since g<n/2, n-g > n/2 > (n-1)/2, and since i>binom(n-1,g), i>binom(n-1,n-g)
                //so by Rule #3: for j = i - binom(n-1,n-g):
                //   basis_blade(n,g,i) == basis_blade(n-1,n-g,j) * psuedoscalar(n-1).inv() * e_n
                //again by Rule #4:
                //   basis_blade(n,g,i) == basis_blade(n-1,(n-1)-(n-g),j) * e_n
                //   basis_blade(n,g,i) == basis_blade(n-1,g-1,j) * e_n
                let prev_dual = Self::basis_blade(n-1, g-1, i-count_prev);
                let new_basis_vector = Self::const_basis_vector(n-1);

                //next, we can just multiply using XOR since
                //it is a right mul by e_n and prev_dual.dim() < n
                BasisBlade { bits: prev_dual.bits ^ new_basis_vector.bits }

            }
        } else {
            //the number of elements of the *dual* grade in the prev dimension
            let count_prev_dual = binom(n-1,n-g);
            if i < count_prev_dual {

                //From Rule #4: for g < n/2:
                //   basis_blade(n,g,i) == basis_blade(n,n-g,i) /
                //   basis_blade(n,g,i) * psuedoscalar(n) == basis_blade(n,n-g,i)
                //   basis_blade(n,n-g,i) == basis_blade(n,g,i) * psuedoscalar(n)
                //so, for g > n/2:
                //   basis_blade(n,g,i) == basis_blade(n,n-g,i) * psuedoscalar(n)

                //next, for i < binom(n-1,n-g)
                //   basis_blade(n,g,i) == basis_blade(n,n-g,i) * psuedoscalar(n)
                //   basis_blade(n,g,i) == basis_blade(n,n-g,i) * e_n * psuedoscalar(n-1)
                //   basis_blade(n,g,i) == (-1)^(n-1) * basis_blade(n,n-g,i) * psuedoscalar(n-1) * e_n
                //since g>n/2 and i<binom(n-1,n-g), n-g < n/2 <= (n-1)/2
                //
                //If n-g < (n-1)/2, by Rule #2:
                //   basis_blade(n,g,i) == (-1)^(n-1) * basis_blade(n-1,n-g,i) * psuedoscalar(n-1) * e_n
                //again by Rule #4:
                //   basis_blade(n,g,i) == (-1)^(n-1) * basis_blade(n-1,(n-1)-(n-g),i) * e_n
                //   basis_blade(n,g,i) == (-1)^(n-1) * basis_blade(n-1,g-1,i) * e_n
                //
                //Else, n-g == (n-1)/2, so by Rule #6:
                //   if i<(n-1)/2:
                //   basis_blade(n,g,i) == (-1)^(n-1) * basis_blade(n-1,n-g,i+binom(n-1,(n-1)-g)) * psuedoscalar(n-1) * e_n
                //   else:
                //   basis_blade(n,g,i) == (-1)^(n-1) (-1)^(n-2) * basis_blade(n-1,n-g,i-binom(n-1,(n-1)-g)) * psuedoscalar(n-1) * e_n
                //

                let j = if g-1 == (n-1)/2 {
                    let c = count_prev_dual;
                    (i+c/2)%c
                } else { i };

                let prev_dual = Self::basis_blade(n-1, g-1, j);
                let new_basis_vector = Self::const_basis_vector(n-1);
                let sign = (((n-1)&1) as Bits) << Self::MAX_DIM;

                //next, we can just multiply using XOR since
                //it is a right mul by e_n and prev_dual.dim() < n
                BasisBlade { bits: prev_dual.bits ^ new_basis_vector.bits ^ sign }
            } else {
                //Rule #3: if g>n/2, and i>binom(n-1, n-g). then the basis is the same as in
                //the previous dimension but with the index shifted down by binom(n-1, n-g).
                Self::basis_blade(n-1,g,i-count_prev_dual)
            }
        }

    }

}

#[test]
fn basis_blade() {

    for n in 0..=5 {
        println!("\nn={}", n);
        for g in 0..=n {

            print!("g={}: ", g);
            for i in 0..binom(n,g) {
                print!("{:7}", BasisBlade::basis_blade(n,g,i));
            }
            println!();
        }
    }

}

impl Binary for BasisBlade {
    fn fmt(&self, f: &mut Formatter) -> FmtResult {
        write!(f, "{:b}", self.bits)
    }
}

impl Debug for BasisBlade {
    fn fmt(&self, f: &mut Formatter) -> FmtResult { Display::fmt(self, f) }
}

impl Display for BasisBlade {
    fn fmt(&self, f: &mut Formatter) -> FmtResult {

        //converts a number into an iterator of subscript characters
        fn subscript_digits(mut n: usize) -> impl Iterator<Item=char> {

            //find the greatest power of 10 less than or equal to n
            let mut div = 1;
            let mut digits = 1;
            while div*10 <= n {
                div *= 10;
                digits += 1;
            }

            //loop from most sig digit to least
            (0..digits).into_iter().map(
                move |_| {
                    let (q, r) = (n/div, n%div);
                    let digit = unsafe { char::from_u32_unchecked(0x2080 + q as u32) };
                    n = r;
                    div /= 10;
                    digit
                }
            )

        }

        let dim = self.dim();
        let grade = self.grade();

        //if we should use a '-' sign instead of swapping
        let minus_mode = f.sign_minus() || grade<=1;

        //if a sign should be printed
        let do_sign = f.sign_plus() || minus_mode && self.negative();

        //if each vector should have it's own 'e'. this is required for dim>=10
        //as if we don't, we get ambiguity on if a digit is another vector or in the 10s place
        let separate_e = dim>=10;

        let num_chars = {
            (if do_sign { 1 } else { 0 }) +
            (if separate_e { 2*grade } else { 1+grade })
        };

        let padding = {
            match f.width() {
                None => 0,
                Some(w) => w.saturating_sub(num_chars)
            }
        };

        //adds the appropriate amount of padding
        let do_padding = |f: &mut Formatter, count| {
            for _ in 0..count {
                write!(f, "{}", f.fill())?
            }
            Ok(())
        };

        //writes a single basis vector with subscript i
        //if dim>=10, it adds an 'e'
        let write_vector = |f: &mut Formatter, i| {
            if separate_e { write!(f, "e")?; }
            for d in subscript_digits(i) {
                write!(f, "{}", d)?;
            }
            Ok(())
        };

        //do the padding on the left
        match f.align() {
            Some(Alignment::Right) => do_padding(f, padding)?,
            Some(Alignment::Center) => do_padding(f, padding/2)?,
            _ => ()
        }

        //for prepending a sign
        if do_sign {
            if self.negative() {
                write!(f, "-")?;
            } else {
                write!(f, "+")?;
            }
        }

        //if the dim<10 we can write all the vectors as subscripts of one 'e'
        if !separate_e { write!(f, "e")?; }

        //if we are in minus mode or positive, we don't want to do any swaps
        if minus_mode || self.positive() {

            //just print out all vectors apart of this blade in ascending order
            for i in 0..Self::MAX_DIM {
                if ((1<<i) & self.bits) != 0 {
                    write_vector(f, i+1)?;
                }
            }

        } else {
            //else, we swap the first two vectors to negate the basis blade

            let mut first = None;
            let mut start = true;

            for i in 0..Self::MAX_DIM {
                if ((1<<i) & self.bits) != 0 {

                    match first {
                        //store the first vector
                        None => first = Some(i),

                        //if we've already stored the first, print the second then the first
                        Some(j) => {
                            write_vector(f, i+1)?;
                            if start {
                                write_vector(f, j+1)?;
                                start = false;
                            }
                        }
                    }

                }
            }

        }

        //do the padding on the left
        match f.align() {
            Some(Alignment::Left) | None => do_padding(f, padding)?,
            Some(Alignment::Center) => do_padding(f, padding - padding/2)?,
            _ => ()
        }

        Ok(())

    }
}

impl One for BasisBlade {
    fn one() -> Self { Self::ONE }
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

        impl<'a> $Assign<&'a BasisBlade> for BasisBlade {
            fn $assign(&mut self, rhs: &'a BasisBlade) { *self = self.$op(rhs) }
        }
    }
}

impl_bin_op!(Mul.mul() MulAssign.mul_assign());
impl_bin_op!(Div.div() DivAssign.div_assign());

#[cfg(test)]
#[allow(non_upper_case_globals)]
mod tests {

    use super::*;

    const e: BasisBlade = BasisBlade::ONE;

    const e1: BasisBlade = BasisBlade::const_basis_vector(0);
    const e2: BasisBlade = BasisBlade::const_basis_vector(1);
    const e3: BasisBlade = BasisBlade::const_basis_vector(2);
    const e4: BasisBlade = BasisBlade::const_basis_vector(3);

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
    fn display() {

        macro_rules! test_fmt {
            ($e:expr; $fmt:literal $neg_alt:literal) => {
                assert_eq!(format!("{:-}", $e), $fmt);
                assert_eq!(format!("{}", $e), $fmt);
                assert_eq!(format!("{:-}", -$e), concat!("-", $fmt));
                assert_eq!(format!("{}", -$e), $neg_alt);

                assert_eq!(format!("{:-?}", $e), $fmt);
                assert_eq!(format!("{:?}", $e), $fmt);
                assert_eq!(format!("{:-?}", -$e), concat!("-", $fmt));
                assert_eq!(format!("{:?}", -$e), $neg_alt);
            }
        }

        assert_eq!(format!("{}", e), "e");
        assert_eq!(format!("{}", -e), "-e");
        test_fmt!(e1; "e₁" "-e₁");
        test_fmt!(e2; "e₂" "-e₂");
        test_fmt!(e3; "e₃" "-e₃");
        test_fmt!(e4; "e₄" "-e₄");
        test_fmt!(e12; "e₁₂" "e₂₁");
        test_fmt!(e13; "e₁₃" "e₃₁");
        test_fmt!(e14; "e₁₄" "e₄₁");
        test_fmt!(e23; "e₂₃" "e₃₂");
        test_fmt!(e24; "e₂₄" "e₄₂");
        test_fmt!(e34; "e₃₄" "e₄₃");
        test_fmt!(e123; "e₁₂₃" "e₂₁₃");
        test_fmt!(e124; "e₁₂₄" "e₂₁₄");
        test_fmt!(e134; "e₁₃₄" "e₃₁₄");
        test_fmt!(e234; "e₂₃₄" "e₃₂₄");
        test_fmt!(e1234; "e₁₂₃₄" "e₂₁₃₄");


        let e9 = BasisBlade::basis_vector(8);

        test_fmt!(e9; "e₉" "-e₉");
        test_fmt!(e1*e9; "e₁₉" "e₉₁");

        //
        //Dims greater than 10
        //

        let e10 = BasisBlade::basis_vector(9);
        let e11 = BasisBlade::basis_vector(10);
        test_fmt!(e10; "e₁₀" "-e₁₀");
        test_fmt!(e11; "e₁₁" "-e₁₁");
        test_fmt!(e10*e11; "e₁₀e₁₁" "e₁₁e₁₀");
        test_fmt!(e1*e11; "e₁e₁₁" "e₁₁e₁");
        test_fmt!(e1*e2*e11; "e₁e₂e₁₁" "e₂e₁e₁₁");


    }

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
                    assert!($e.positive());
                    assert!(!$e.negative());
                    assert!((-$e).negative());
                    assert!(!(-$e).positive());
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
                $(test_mul!(one*$e == $e; true);)*
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
