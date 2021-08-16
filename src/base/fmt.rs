
use super::*;

struct FmtElement<'a, T, F>(&'a T, F) where F: Fn(&T, &mut Formatter) -> FmtResult;

impl<'a, T, F> Debug for FmtElement<'a, T, F> where F: Fn(&T, &mut Formatter) -> FmtResult {
    fn fmt(&self, f: &mut Formatter) -> FmtResult { (self.1)(self.0, f) }
}

struct FmtAlgebra<'a, T, B, F>(&'a [T], B, F) where
    F: Fn(&T, &mut Formatter) -> FmtResult,
    B: Fn(usize) -> Option<BasisBlade>;

impl<'a, T, B, F> Debug for FmtAlgebra<'a, T, B, F>
where
    F: Fn(&T, &mut Formatter) -> FmtResult,
    B: Fn(usize) -> Option<BasisBlade>
{
    fn fmt(&self, f: &mut Formatter) -> FmtResult {

        let do_sum = f.sign_plus();
        let FmtAlgebra(data, basis, fmt_t) = self;
        let len = data.len();

        match f.width() {

            //if there is no padding
            None => {

                if do_sum {

                    if len > 0 {

                        for i in 0..len {

                            //write to a temp string
                            let temp = format!("{:?}", FmtElement(&data[i], fmt_t));

                            //remove any excess whitespace
                            let element = temp.trim();

                            //determine if positive or negative and remove the sign
                            let (negative, remove_sign) = match element.chars().next() {
                                Some('+') => (false, true),
                                Some('-') => (true, true),
                                _ => (false, false)
                            };

                            //remove the + or - sign
                            let element = if remove_sign { &element[1..] } else { element };

                            //next, determine if we need to add parens
                            let mut level = 0i32;
                            let mut add_parens = false;
                            for c in element.chars() {
                                match c {
                                    //if there's already parens of some sort, we don't need parens
                                    '(' | '[' | '{' => level += 1,
                                    ')' | ']' | '}' => level -= 1,

                                    //if the element is itself a sum or non mul operation,
                                    //we need to add parens
                                    '+' | '-' | '/' | '%' | '&' | '|' | '^'
                                    => if level <= 0 {
                                        add_parens=true;
                                        break;
                                    },
                                    _ => ()
                                }
                            }

                            //TODO: if the basis is 1, we can get rid of parens

                            //if something wonky is going on and the parens aren't
                            //closed or opened, just add parens anyways...
                            if level != 0 { add_parens = true }

                            //TODO: if the element is 1 or 0, we can simplify the string a little bit

                            //write the sign
                            match (i==0, negative) {
                                (false, false) => write!(f, " + ")?,
                                (false, true)  => write!(f, " - ")?,
                                (true,  true)  => write!(f, "-")?,
                                _ => ()
                            };

                            //write the element
                            if add_parens {
                                write!(f, "({})", element)?;
                            } else {
                                write!(f, "{}", element)?;
                            }

                            //get the basis blade
                            if let Some(b) = basis(i) {
                                //write the basis blade if it is not one
                                if !b.is_one() {
                                    write!(f, "{}", b)?;
                                }
                            }

                        }

                        Ok(())

                    } else {
                        //the empty sum is 0
                        write!(f, "0")
                    }

                } else {
                    write!(f, "[")?;
                    for i in 0..len {
                        //write the value at i
                        fmt_t(&data[i], f)?;

                        //insert a comma if not at the end
                        if i+1 < self.0.len() { write!(f, ", ")?; }
                    }
                    write!(f, "]")
                }

            },

            //if there is padding
            Some(_) => {
                //write to a temp string
                let no_padding = if do_sum { format!("{:+?}", *self) } else { format!("{:?}", *self) };

                //pad the temp string
                f.pad(&no_padding)
            }
        }

    }
}

macro_rules! impl_fmt {

    //loop over every fmt trait
    (;$($rest:tt)*) => {};
    ($Fmt:ident $symbol:literal $(, $F:ident $s:literal)*; $Ty:ident<T:$Alloc:ident $(, $N:ident)*>) => {
        impl<T:$Alloc<$($N),*>+$Fmt $(, $N:Dim)*> $Fmt for $Ty<T $(, $N)*> {
            fn fmt(&self, f: &mut Formatter) -> FmtResult {

                let (alt, prec) = (f.alternate(), f.precision());

                Debug::fmt(
                    &FmtAlgebra(
                        self.as_slice(),
                        |i| Some(self.basis(i)),
                        |t, dest| match (alt, prec) {
                            (false, None)    => write!(dest, concat!("{:", $symbol, "}"), t),
                            (false, Some(p)) => write!(dest, concat!("{:.1$", $symbol, "}"), t, p),
                            (true,  None)    => write!(dest, concat!("{:#", $symbol, "}"), t),
                            (true,  Some(p)) => write!(dest, concat!("{:#.1$", $symbol, "}"), t, p),
                        }
                    ),
                    f
                )


            }
        }

        impl_fmt!($($F $s),*; $Ty<T:$Alloc $(, $N)*>);
    };

    //loop over each type
    ($($Fmt:ident $symbol:literal),*;) => {};
    ($($Fmt:ident $symbol:literal),*; $Ty:ident<T:$Alloc:ident $(, $N:ident)*> $($rest:tt)*) => {
        impl_fmt!($($Fmt $symbol),*; $Ty<T:$Alloc $(, $N)*>);
        impl_fmt!($($Fmt $symbol),*; $($rest)*);
    };



}

impl_fmt!(
    Display "", Binary "b", Octal "o", LowerHex "x", UpperHex "X", LowerExp "e", UpperExp "E";
    Blade<T:AllocBlade,N,G> Even<T:AllocEven,N> Odd<T:AllocOdd,N> Multivector<T:AllocMultivector,N>
);

#[cfg(test)]
mod tests {

    use super::*;

    #[test]
    fn print() {

        // for n in 0..=6 {
        //     println!("n={}", n);
        //     for g in 0..=n {
        //         println!("{}", BladeD::from_iterator(n, g, 1..));
        //     }
        //     println!();
        // }
        //
        // println!();
        //
        // for n in 0..=6 {
        //     println!("n={}", n);
        //     for g in 0..=n {
        //         println!("{:+}", BladeD::from_iterator(n, g, -3..));
        //     }
        //     println!();
        // }

    }



}
