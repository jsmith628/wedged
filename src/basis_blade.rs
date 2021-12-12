
use num_traits::{One, Inv};
use std::ops::{Neg, Mul, MulAssign, Div, DivAssign};
use std::fmt::{Formatter, Debug, Display, Binary, Result as FmtResult, Alignment};

use crate::base::*;

//So we can maybe change it later though there really is no reason it needs any more bits than this
pub type Bits = i32;

#[repr(transparent)]
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct BasisBlade {
    pub bits: Bits
}

impl BasisBlade {

    ///The maximum number of dimensions supported
    pub const MAX_DIM: usize = (Bits::BITS - 1) as usize; //the bit width minus one for the sign

    ///The multiplicative identity
    pub const ONE: BasisBlade = BasisBlade { bits: 0 }; //1 is just the empty product (ie when bits==0)

    ///Negative one
    pub const NEG_ONE: BasisBlade = BasisBlade { bits: Bits::MIN }; //0 with the leading bit flipped

    ///
    /// Quickly does `(-1)^n`
    ///
    #[inline(always)]
    const fn neg_one_pow(n:usize) -> BasisBlade {
        BasisBlade { bits:((n & 1) as Bits) << Self::MAX_DIM }
    }

    ///
    /// Multiplies two basis blades quickly by using only XOR
    ///
    /// This **only** works if `self.dim()` is less than or equal to the min dim of the vectors
    /// in `rhs`, as this is the only way to guarantee that we don't need any swaps
    ///
    #[inline(always)]
    const fn unchecked_fast_mul(self, rhs: BasisBlade) -> BasisBlade {
        BasisBlade { bits: self.bits ^ rhs.bits }
    }

    pub const fn from_bits(bits:Bits) -> BasisBlade { BasisBlade { bits } }

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

    /// Reverses the order of the vectors making up this basis element
    pub const fn reverse(self) -> Self {
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

    /// Negates if [`grade`](BasisBlade::grade) is odd
    pub const fn involute(self) -> Self {
        self.unchecked_fast_mul(Self::neg_one_pow(self.grade()))
    }

    pub const fn const_mul(self, rhs: Self) -> Self {
        //we only have to abs() self since it will mask out the sign of rhs
        let a = self.abs().bits;
        let b = rhs.bits;

        //compute the sign of the result by computing the number of swaps
        //required to align all the basis vectors

        const fn compute_swaps(a: Bits, b: Bits) -> usize {
            if a==0 {
                0
            } else {
                (a&b).count_ones() as usize + compute_swaps(a>>1, b)
            }
        }
        let swaps = compute_swaps(a >> 1, b);

        //if swaps is even, this is 0, if it is odd, it is Bits::MIN
        let sign = Self::neg_one_pow(swaps);

        //xor everything together
        //self.bits ^ rhs.bits selects out all basis vectors not in common
        //^ sign flips the sign according to the swaps we had to do
        self.unchecked_fast_mul(rhs).unchecked_fast_mul(sign)
    }

    pub const fn const_div(self, rhs: Self) -> Self { self.const_mul(rhs.reverse()) }

    ///
    /// Returns the nth basis vector
    ///
    /// Panics if n is greater than the maximum dimension
    ///
    pub fn basis_vector(n: usize) -> BasisBlade {
        if n >= Self::MAX_DIM {
            panic!("Only Vectors up to dimension {} are currently supported", Self::MAX_DIM )
        }
        BasisBlade::const_basis_vector(n)
    }

    ///
    /// Returns the nth basis vector
    ///
    /// Returns `BasisBlade::one()` if n is greater than the maximum dimension
    ///
    pub const fn const_basis_vector(n: usize) -> BasisBlade {
        BasisBlade { bits: 1 << n }.abs()
    }

    pub fn basis_blade(n:usize, g:usize, i:usize) -> BasisBlade {
        if n >= Self::MAX_DIM {
            panic!("Only Blades up to dimension {} are currently supported", Self::MAX_DIM );
        }

        if g>n || i>binom(n,g) {
            panic!("No basis {}-dimensional blade of grade {} at index {}", n, g, i);
        }

        Self::const_basis_blade(n, g, i)

    }

    //Rule #0: if grade==0, then the basis is just the identity
    //Rule #1: if grade==1, then the basis is e_i
    //Rule #2: if g<=n/2 and i<binom(n-1,g), then basis_blade(n,g,i) == basis_blade(n-1,g,i)
    //Rule #3: if g> n/2 and i>binom(n-1,n-g), then
    //      basis_blade(n,g,i) == basis_blade(n-1,g,i-binom(n-1,n-g))
    //
    //Rule #4: for g<n/2, basis_blade(n,g,i) == basis_blade(n,n-g,i) / psuedoscalar(n)
    //Lemma #1: for g>n/2, basis_blade(n,g,i) == basis_blade(n,n-g,i) * psuedoscalar(n)
    //
    //Rule #5: for g==n/2, i<binom(n,g)/2,
    //      basis_blade(n,g,i) == basis_blade(n,n-g,i+binom(n,g)/2) / psuedoscalar(n)
    //
    //Lemma #2: for g==n/2, i>binom(n,g)/2,
    //      basis_blade(n,g,i) == basis_blade(n,n-g,i-binom(n,g)/2) * psuedoscalar(n)


    const fn const_undual_basis(n:usize, g:usize, i:usize) -> BasisBlade {

        //invalid basis vectors
        if g>n || i>binom(n,g) { return Self::ONE; }

        if 2*g < n {
            //Rule #3
            Self::const_basis_blade(n, n-g, i)
        } else if 2*g == n {

            //Rule #5
            let prev_count = binom(n,g)/2;
            if i < prev_count {
                Self::const_basis_blade(n, g, i + prev_count)
            } else {
                let sign = Self::neg_one_pow(n*(n-1)/2);
                Self::const_basis_blade(n, g, i - prev_count).unchecked_fast_mul(sign)
            }

        } else {
            //Rule #4
            //the sign converts from dual to undual
            let sign = Self::neg_one_pow(n*(n-1)/2);
            Self::const_basis_blade(n, n-g, i).unchecked_fast_mul(sign)
        }


    }

    pub const fn const_basis_blade(n:usize, g:usize, i:usize) -> BasisBlade {

        //invalid basis vectors
        if g>n || i>binom(n,g) { return Self::ONE; }

        //From Rule #0
        if g==0 { return Self::ONE; }

        //From Rule #1
        if g==1 { return Self::const_basis_vector(i); }

        //The below optimizations for applying Rules 4-5 only work for n>2, so we hardcode n==2
        if n==2 && g==2 && i==0 { return BasisBlade { bits: 0b11 }; }

        if 2*g < n {
            //the number of elements of this grade in the prev dimension
            let count_prev = binom(n-1,g);

            if i < count_prev {
                //From Rule #2
                Self::const_basis_blade(n-1,g,i)
            } else {

                //From Rule #4:
                //  basis_blade(n,g,i) = basis_blade(n,n-g,i) / psuedoscalar(n)
                //Since g < n/2, n-g > n/2, and
                //Since i > binom(n-1, g) = binom(n-1, n - (n-g))
                //By Rule #3: letting j = i-binom(n-1, n - (n-g)) = i - binom(n-1, g)
                //  basis_blade(n,g,i) = basis_blade(n-1,n-g,j) / psuedoscalar(n)
                //  basis_blade(n,g,i) = basis_blade(n-1,n-g,j) * psuedoscalar(n).inv()
                //  basis_blade(n,g,i) = basis_blade(n-1,n-g,j) * (e_n * psuedoscalar(n-1)).inv()
                //  basis_blade(n,g,i) = basis_blade(n-1,n-g,j) * psuedoscalar(n-1).inv() * e_n
                //  basis_blade(n,g,i) = (basis_blade(n-1,n-g,j) / psuedoscalar(n-1)) * e_n
                //Now since n-g > n/2, n-g > (n-1)/2, so:
                //From Rule #4 again:
                //  basis_blade(n,g,i) = basis_blade(n-1,(n-1)-(n-g),j) * e_n
                //  basis_blade(n,g,i) = basis_blade(n-1,g-1,j) * e_n

                let j = i - count_prev;
                let prev_blade = Self::const_basis_blade(n-1, g-1, j);
                let e_n = Self::const_basis_vector(n-1);

                //since prev_blade.dim() < n and we're doing right-mul by e_n, we can just
                //multiply by doing the XOR of the bits
                BasisBlade { bits: prev_blade.bits ^ e_n.bits }

            }
        } else if 2*g==n {
            //the number of elements of this grade in the prev dimension
            let count = binom(n,g);

            if i < count/2 {
                //From Rule #2
                Self::const_basis_blade(n-1,g,i)
            } else {
                //From Lemma #2 we can derive a fact very similar to the above using the
                //exact same logic

                //TODO: explain

                let j = i - count/2;
                let prev_blade = Self::const_basis_blade(n-1, g-1, j);
                let e_n = Self::const_basis_vector(n-1);
                let sign = Self::neg_one_pow((n-1) * n * (n-1) / 2);

                //like above, we can mul just using XOR
                prev_blade.unchecked_fast_mul(e_n).unchecked_fast_mul(sign)
            }
        } else {
            //the number of elements of the *dual* grade in the prev dimension
            let count_prev_dual = binom(n-1, n-g);
            if i < count_prev_dual {

                //From Lemma #1
                //  basis_blade(n,g,i) = basis_blade(n,n-g,i) * psuedoscalar(n)
                //Since g > n/2, n-g < n/2
                //Since i < binom(n-1, n-g)
                //By Rule #3:
                //  basis_blade(n,g,i) = basis_blade(n-1,n-g,i) * psuedoscalar(n)
                //  basis_blade(n,g,i) = basis_blade(n-1,n-g,i) * e_n * psuedoscalar(n-1)
                //  basis_blade(n,g,i) = (-1)^n * basis_blade(n-1,n-g,i) * psuedoscalar(n-1) * e_n
                //Now we have two cases:
                //If g > (n-1)/2: We can use Rule #4 again:
                //  basis_blade(n,g,i) = (-1)^n * basis_blade(n-1,(n-1)-(n-g),i) * e_n
                //  basis_blade(n,g,i) = (-1)^n * basis_blade(n-1,g-1,i) * e_n
                //Else: g-1 == (n-1)/2, and we use Rule #5:
                //  basis_blade(n,g,i) = (-1)^n * basis_blade(n-1,(n-1)-(n-g),j) * e_n
                //  basis_blade(n,g,i) = (-1)^n * basis_blade(n-1,g-1,j) * e_n
                //where j = i+binom(n-1,g-1)/2 if i<binom(n-1,g-1)/2 or j = i-binom(n-1,g-1)/2 otherwise

                let prev_blade = Self::const_undual_basis(n-1,n-g,i);
                let e_n = Self::const_basis_vector(n-1);
                let sign = Self::neg_one_pow(n-1);

                //like above, we can multiply everything together just using XOR
                prev_blade.unchecked_fast_mul(e_n).unchecked_fast_mul(sign)

            } else {
                //From Rule #3
                Self::const_basis_blade(n-1,g,i-count_prev_dual)
            }
        }

    }

    pub fn basis_even(n: usize, i: usize) -> BasisBlade {
        let mut i = i;
        for (g, binom) in components_of(n).enumerate().step_by(2) {
            if binom > i {
                return Self::basis_blade(n,g,i);
            } else {
                i -= binom;
            }
        }

        panic!("index out of range: {}>{}", i, even_elements(n))
    }

    pub fn basis_odd(n: usize, i: usize) -> BasisBlade {
        let mut i = i;
        for (g, binom) in components_of(n).enumerate().skip(1).step_by(2) {
            if binom > i {
                return Self::basis_blade(n,g,i);
            } else {
                i -= binom;
            }
        }

        panic!("index out of range: {}>{}", i, odd_elements(n))
    }

    pub fn basis(n: usize, i: usize) -> BasisBlade {
        let mut i = i;
        for (g, binom) in components_of(n).enumerate() {
            if binom > i {
                return Self::basis_blade(n,g,i);
            } else {
                i -= binom;
            }
        }

        panic!("index out of range: {}>{}", i, multivector_elements(n))
    }

    const fn get_index_sign_in(self, n: usize, g: usize) -> (usize, bool) {

        //TODO: explain

        const fn sign_pow(n: usize) -> bool { (n&1)==1 }

        if n==0 || g==0 { return (0, self.positive()); }

        let e_n = Self::const_basis_vector(n-1);
        let contains_e_n = (self.bits & e_n.bits) != 0;

        if g == 1 {
            if contains_e_n { (n-1, self.positive()) } else { self.get_index_sign_in(n-1, g) }
        } else if 2*g < n {
            if contains_e_n {
                let (index, sign) = self.unchecked_fast_mul(e_n).get_index_sign_in(n-1, g-1);
                (index + binom(n-1, g), sign)
            } else {
                self.get_index_sign_in(n-1, g)
            }
        } else if 2*g == n {
            if contains_e_n {
                let (index, sign) = self.unchecked_fast_mul(e_n).get_index_sign_in(n-1, g-1);
                (index + binom(n-1, g), sign ^ sign_pow((n-1) * n * (n-1) / 2))
            } else {
                self.get_index_sign_in(n-1, g)
            }
        } else {
            if contains_e_n {

                let (index, sign) = self.unchecked_fast_mul(e_n).get_index_sign_in(n-1, g-1);
                let sign = sign ^ sign_pow(n-1);

                if 2*(g-1) == n-1 {
                    let count = binom(n-1, g-1);
                    if index < count/2 {
                        ((index + count/2), sign ^ sign_pow(n * (n-1) / 2))
                    } else {
                        ((index - count/2), sign)
                    }
                } else if g==2 && n==2 {
                    (index, self.positive())
                } else {
                    (index, sign)
                }

            } else {
                let (index, sign) = self.get_index_sign_in(n-1, g);
                (index + binom(n-1, n-g), sign)
            }
        }

    }

    pub const fn blade_index_sign(&self, n: usize) -> (usize, bool) {
        let n = if n > Self::MAX_DIM { Self::MAX_DIM } else { n };
        self.get_index_sign_in(n, self.grade())
    }

    pub const fn even_index_sign(&self, n: usize) -> (usize, bool) {
        if self.grade()%2 == 1 { return (0,self.positive()); }
        let (i, sign) = self.blade_index_sign(n);

        //TODO: optimize by having a progressive value of the binomial coefficient
        const fn get_start(n:usize, g:usize) -> usize {
            if g<=1 { return 0; }
            get_start(n, g-2) + binom(n,g-2)
        }

        (get_start(n,self.grade()) + i, sign)
    }

    pub const fn odd_index_sign(&self, n: usize) -> (usize, bool) {
        if self.grade()%2 == 0 { return (0,self.positive()); }
        let (i, sign) = self.blade_index_sign(n);

        //TODO: optimize by having a progressive value of the binomial coefficient
        const fn get_start(n:usize, g:usize) -> usize {
            if g<=1 { return 0; }
            get_start(n, g-2) + binom(n,g-2)
        }

        (get_start(n,self.grade()) + i, sign)
    }

    pub const fn multivector_index_sign(&self, n: usize) -> (usize, bool) {
        let (i, sign) = self.blade_index_sign(n);

        const fn get_start(n:usize, g:usize) -> usize {
            if g==0 { return 0; }
            get_start(n, g-1) + binom(n,g-1)
        }

        (get_start(n,self.grade()) + i, sign)
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
    fn inv(self) -> Self { self.reverse() }
}

impl Mul for BasisBlade {
    type Output = Self;
    fn mul(self, rhs: Self) -> Self { self.const_mul(rhs) }
}

impl Div for BasisBlade {
    type Output = Self;
    fn div(self, rhs: Self) -> Self { self.const_div(rhs) }
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



    #[test]
    fn basis() {

        // for n in 0..=6 {
        //     println!("\nn={}", n);
        //     for g in 0..=n {
        //
        //         print!("g={}: ", g);
        //         for i in 0..binom(n,g) {
        //             print!("{:7}", BasisBlade::basis_blade(n,g,i));
        //         }
        //         println!();
        //     }
        // }

        assert_eq!(e, BasisBlade::basis_blade(0,0,0));

        assert_eq!(e,  BasisBlade::basis_blade(1,0,0));
        assert_eq!(e1, BasisBlade::basis_blade(1,1,0));

        assert_eq!(e,   BasisBlade::basis_blade(2,0,0));
        assert_eq!(e1,  BasisBlade::basis_blade(2,1,0));
        assert_eq!(e2,  BasisBlade::basis_blade(2,1,1));
        assert_eq!(e12, BasisBlade::basis_blade(2,2,0));

        assert_eq!(e,     BasisBlade::basis_blade(3,0,0));
        assert_eq!(e1,    BasisBlade::basis_blade(3,1,0));
        assert_eq!(e2,    BasisBlade::basis_blade(3,1,1));
        assert_eq!(e3,    BasisBlade::basis_blade(3,1,2));
        assert_eq!(e2*e3, BasisBlade::basis_blade(3,2,0));
        assert_eq!(e3*e1, BasisBlade::basis_blade(3,2,1));
        assert_eq!(e1*e2, BasisBlade::basis_blade(3,2,2));
        assert_eq!(e123,  BasisBlade::basis_blade(3,3,0));

    }

    #[test]
    fn basis_rule_1() {
        for n in 0..BasisBlade::MAX_DIM {
            for i in 0..n {
                assert_eq!(BasisBlade::basis_blade(n,1,i), BasisBlade::basis_vector(i));
            }
        }
    }

    #[test]
    fn basis_rule_2_3() {
        for n in 1..=16 {
            for g in 0..=(n-1) {
                let count = binom(n,g);
                if 2*g <= n {
                    //Rule #2
                    let prev_count = binom(n-1,g);
                    for i in 0..prev_count {
                        assert_eq!(
                            BasisBlade::basis_blade(n,g,i),
                            BasisBlade::basis_blade(n-1,g,i)
                        );
                    }
                } else {
                    //Rule #3
                    let prev_count = binom(n-1,n-g);
                    for i in prev_count..count {
                        assert_eq!(
                            BasisBlade::basis_blade(n,g,i),
                            BasisBlade::basis_blade(n-1,g,i-prev_count)
                        );
                    }
                }
            }

        }
    }

    #[test]
    fn basis_rule_4_5() {
        for n in 1..=16 {
            for g in 0..=n {
                let count = binom(n,g);
                let ps = BasisBlade::basis_blade(n,n,0);
                if 2*g < n {
                    let prev_count = binom(n-1,g);
                    for i in 0..prev_count {
                        assert_eq!(
                            BasisBlade::basis_blade(n,g,i),
                            BasisBlade::basis_blade(n,n-g,i) / ps
                        );
                    }
                } else if 2*g == n {
                    for i in 0..count/2 {
                        assert_eq!(
                            BasisBlade::basis_blade(n,g,i),
                            BasisBlade::basis_blade(n,g,i+count/2) / ps
                        );
                        assert_eq!(
                            BasisBlade::basis_blade(n,g,i+count/2),
                            BasisBlade::basis_blade(n,g,i) * ps
                        );
                    }
                } else {
                    let prev_count = binom(n-1,n-g);
                    for i in prev_count..count {
                        assert_eq!(
                            BasisBlade::basis_blade(n,g,i),
                            BasisBlade::basis_blade(n,n-g,i) * ps
                        );
                    }
                }
            }

        }
    }

    #[test]
    fn blade_index() {
        for n in 1..=16 {
            // println!("\nn = {}:", n);
            for g in 0..=n {
                for i in 0..binom(n,g) {
                    let blade = BasisBlade::basis_blade(n,g,i);
                    // print!("{:?} ", blade.get_index_sign(n));
                    assert_eq!((i, true), blade.blade_index_sign(n));
                    assert_eq!((i, false), (-blade).blade_index_sign(n));
                }
                // println!();
            }
        }
    }

    #[test]
    fn even_index() {
        for n in 1..=16 {
            // println!("\nn = {}:", n);
            for i in 0..(1<<(n/2)) {
                let even = BasisBlade::basis_even(n,i);
                // print!("{:?} ", even.even_index_sign(n));
                assert_eq!((i, true), even.even_index_sign(n));
                assert_eq!((i, false), (-even).even_index_sign(n));
            }
        }
    }

    #[test]
    fn multivector_index() {
        for n in 1..=16 {
            for i in 0..(1<<n) {
                let mv = BasisBlade::basis(n,i);
                assert_eq!((i, true), mv.multivector_index_sign(n));
                assert_eq!((i, false), (-mv).multivector_index_sign(n));
            }
        }
    }

    macro_rules! test_index {
        ($($e:expr; $n:expr, $blade:expr, $even:expr, $mv:expr;)*) => {
            $(
                assert_eq!($e.blade_index_sign($n).0, $blade);
                assert_eq!($e.even_index_sign($n).0, $even);
                assert_eq!($e.multivector_index_sign($n).0, $mv);
            )*
        }
    }

    #[test]
    fn index_2d() {
        test_index!(
             e    ; 2, 0, 0, 0;
             e1   ; 2, 0, 0, 1;
             e2   ; 2, 1, 0, 2;
             e12  ; 2, 0, 1, 3;
        );
    }

    #[test]
    fn index_3d() {
        test_index!(
             e    ; 3, 0, 0, 0;
             e1   ; 3, 0, 0, 1;
             e2   ; 3, 1, 0, 2;
             e3   ; 3, 2, 0, 3;
             e23  ; 3, 0, 1, 4;
            -e13  ; 3, 1, 2, 5;
             e12  ; 3, 2, 3, 6;
             e123 ; 3, 0, 0, 7;
        );
    }

    #[test]
    fn index_4d() {
        test_index!(
             e     ; 4, 0, 0, 0;
             e1    ; 4, 0, 0, 1;
             e2    ; 4, 1, 0, 2;
             e3    ; 4, 2, 0, 3;
             e4    ; 4, 3, 0, 4;
             e23   ; 4, 0, 1, 5;
            -e13   ; 4, 1, 2, 6;
             e12   ; 4, 2, 3, 7;
             e14   ; 4, 3, 4, 8;
             e24   ; 4, 4, 5, 9;
             e34   ; 4, 5, 6, 10;
            -e234  ; 4, 0, 0, 11;
             e134  ; 4, 1, 0, 12;
            -e124  ; 4, 2, 0, 13;
             e123  ; 4, 3, 0, 14;
            -e1234 ; 4, 0, 7, 15;
        );
    }


}
