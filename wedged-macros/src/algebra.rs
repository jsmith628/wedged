
use basis_blade::*;
use proc_macro2::*;
use quote::*;
use std::iter::*;

#[derive(Clone, Copy, Hash, PartialEq, Eq, Debug)]
pub enum AlgebraKind {
    Blade, Even, Odd, Full
}

impl ToTokens for AlgebraKind {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        tokens.extend(
            match self {
                AlgebraKind::Blade => quote!(Blade),
                AlgebraKind::Even => quote!(Even),
                AlgebraKind::Odd => quote!(Odd),
                AlgebraKind::Full => quote!(Multivector),
            }
        )
    }
}

impl AlgebraKind {

    pub fn iter_at(self, n:usize) -> impl Iterator<Item=Algebra> {

        let iter: Box<dyn Iterator<Item=Algebra>> = match self {
            AlgebraKind::Blade => Box::new((0..=n).map(move |g| Algebra::Blade(n,g))),
            AlgebraKind::Even => Box::new(once(Algebra::Even(n))),
            AlgebraKind::Odd => Box::new(once(Algebra::Odd(n))),
            AlgebraKind::Full => Box::new(once(Algebra::Full(n))),
        };

        iter

    }

    pub fn even(self) -> bool {
        match self {
            AlgebraKind::Even => true,
            _ => false
        }
    }

    pub fn odd(self) -> bool {
        match self {
            AlgebraKind::Odd => true,
            _ => false
        }
    }

}

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

    #[allow(dead_code)]
    pub fn kind(self) -> AlgebraKind {
        match self {
            Algebra::Blade(_,_) => AlgebraKind::Blade,
            Algebra::Even(_) => AlgebraKind::Even,
            Algebra::Odd(_) => AlgebraKind::Odd,
            Algebra::Full(_) => AlgebraKind::Full,
        }
    }


    #[allow(dead_code)]
    pub fn even(self) -> bool {
        match self {
            Algebra::Blade(_,g) => g&1 == 0,
            Algebra::Even(_) => true,
            _ => false
        }
    }

    #[allow(dead_code)]
    pub fn odd(self) -> bool {
        match self {
            Algebra::Blade(_,g) => g&1 != 0,
            Algebra::Odd(_) => true,
            _ => false
        }
    }

    #[allow(dead_code)]
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
