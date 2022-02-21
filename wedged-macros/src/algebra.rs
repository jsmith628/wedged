
use basis_blade::*;
use proc_macro2::*;
use quote::*;
use std::iter::*;

#[derive(Clone, Copy, Hash, PartialEq, Eq, Debug)]
pub enum Algebra {
    Blade(usize, usize),
    Even(usize),
    Odd(usize),
    Full(usize)
}

impl ToTokens for Algebra {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        tokens.extend(
            match self {
                Algebra::Blade(n, g) => quote!(Subspace::Blade(#n, #g)),
                Algebra::Even(n) => quote!(Subspace::Even(#n)),
                Algebra::Odd(n) => quote!(Subspace::Odd(#n)),
                Algebra::Full(n) => quote!(Subspace::Full(#n)),
            }
        )
    }
}

impl Algebra {

    pub fn all_src_in_dim(n:usize) -> impl Iterator<Item=Algebra> + Clone {
        (1..n).map(move |g| Algebra::Blade(n, g))
        .chain(once(Algebra::Even(n)))
        .chain(once(Algebra::Odd(n)))
        .chain(once(Algebra::Full(n)))
    }

    pub fn all_dst(self, rhs:Algebra) -> impl Iterator<Item=Algebra> + Clone {
        use Algebra::*;
        let n = self.dim().max(rhs.dim());

        match (self, rhs) {

            (Blade(_, g1), Blade(_, g2)) => {

                let gmax = g1+g2;
                let gmin = if g1>=g2 { g1-g2 } else { g2-g1 };
                let even = |x| (x&1)==0;

                //every grade outside this range is 0
                (gmin..=gmax)
                //if the grade-sum is even, remove the odds,
                //if the grade-sum is odd, remove the evens
                //because they are all zero and they are a special case
                .filter(|g| even(gmax) == even(*g))
                //we have a special case for the dot-product
                .filter(|g| g1!=g2 || *g!=0)
                //we have a special case for the psuedoscalar dot-product (unless the grades are the same :/)
                .filter(|g| g1+g2!=n || *g!=n || g1==g2)
                .map(move |g| Blade(n,g))

                .chain(once(
                    //only implement an even or odd product if it is non-zero
                    if even(gmax) { Even(n) } else { Odd(n) } )
                )
                .chain(once(Full(n)))

                //turn into a vector iterator to make the type the same as the below
                .collect::<Vec<_>>()
                .into_iter()
            },

            (lhs, rhs) => {

                let mut list = vec![];

                //don't even bother with partial products or blade results, they're not really
                //necessary and dramatically slow comp times
                if lhs.even() && rhs.even() { list.push(Even(n)); }
                if lhs.even() && rhs.odd()  { list.push(Odd(n)); }
                if lhs.odd()  && rhs.even() { list.push(Odd(n)); }
                if lhs.odd()  && rhs.odd()  { list.push(Even(n)); }
                list.push(Full(n));

                list.into_iter()

            }


        }
    }

    pub fn even(self) -> bool {
        match self {
            Algebra::Blade(_,g) => g&1 == 0,
            Algebra::Even(_) => true,
            _ => false
        }
    }

    pub fn odd(self) -> bool {
        match self {
            Algebra::Blade(_,g) => g&1 != 0,
            Algebra::Odd(_) => true,
            _ => false
        }
    }

    pub fn dim(self) -> usize {
        match self {
            Algebra::Blade(n, _) => n,
            Algebra::Even(n) => n,
            Algebra::Odd(n) => n,
            Algebra::Full(n) => n
        }
    }

    pub fn elements(self) -> usize {
        match self {
            Algebra::Blade(n, g) => binom(n, g),
            Algebra::Even(n) => if n==0 { 1 } else { 1 << (n-1) },
            Algebra::Odd(n) => if n==0 { 0 } else { 1 << (n-1) },
            Algebra::Full(n) => 1 << n
        }
    }

    pub fn basis(self, i:usize) -> BasisBlade {
        match self {
            Algebra::Blade(n, g) => BasisBlade::basis_blade(n, g, i),
            Algebra::Even(n) => BasisBlade::basis_even(n, i),
            Algebra::Odd(n) => BasisBlade::basis_odd(n, i),
            Algebra::Full(n) => BasisBlade::basis(n, i)
        }
    }

    pub fn bases(self) -> impl Iterator<Item=(usize, BasisBlade)> + Clone {
        (0..self.elements()).map(move |i| self.basis(i)).enumerate()
    }

    pub fn index_of(self, b:BasisBlade) -> Option<(usize, bool)> {
        match self {
            Algebra::Blade(n, g) if b.grade()==g && b.dim()<=n => Some(b.blade_index_sign(n)),
            Algebra::Even(n) if b.dim()<=n => Some(b.even_index_sign(n)),
            Algebra::Odd(n) if b.dim()<=n => Some(b.odd_index_sign(n)),
            Algebra::Full(n) if b.dim()<=n => Some(b.multivector_index_sign(n)),
            _ => None
        }
    }

}
