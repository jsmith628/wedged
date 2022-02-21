
extern crate proc_macro;
extern crate proc_macro2;
extern crate quote;
extern crate basis_blade;


use quote::*;
use proc_macro2::*;
use basis_blade::*;
use std::iter::*;

#[derive(Clone, Copy, Hash, PartialEq, Eq, Debug)]
enum Algebra {
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

    pub fn all_dst(self, lhs:Algebra) -> impl Iterator<Item=Algebra> + Clone {
        use Algebra::*;
        let n = self.dim().max(lhs.dim());

        match (self, lhs) {

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

            (rhs, lhs) => {

                let mut list = vec![];

                //don't even bother with partial products or blade results, they're not really
                //necessary and dramatically slow comp times
                if rhs.even() && lhs.even() { list.push(Even(n)); }
                if rhs.even() && lhs.odd()  { list.push(Odd(n)); }
                if rhs.odd()  && lhs.even() { list.push(Odd(n)); }
                if rhs.odd()  && lhs.odd()  { list.push(Even(n)); }
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


fn gen_mul_raw<'a,I1,I2,F>(
    rhs:Ident, lhs:Ident, dest:Ident, bases1:I1, bases2:I2, index_of:F, count:usize
) -> TokenStream
where
    I1: Iterator<Item = (usize, BasisBlade)>,
    I2: Iterator<Item = (usize, BasisBlade)>+Clone,
    F: Fn(BasisBlade) -> Option<(usize, bool)>
{

    if count==0 { return TokenStream::new(); }

    //the list of assignments to each component of the destination value
    let mut assignments: Vec<Option<TokenStream>> = vec![None; count];

    //loop over every pair of basis vectors
    for (i, b1) in bases1 {
        for (j, b2) in bases2.clone() {

            //find the basis of the result and its index
            let b3 = b1 * b2;

            if let Some((index, sign)) = index_of(b3) {

                //tokens for multiplying the components of the rhs and lhs
                let term = quote!( #rhs.get(#i).ref_mul(#lhs.get(#j)) );

                //add this term to the corresponding coordinate
                assignments[index] = match (&assignments[index], sign) {
                    (None, true) => Some(term),
                    (None, false) => Some(quote!(- #term)),
                    (Some(a), true) => Some(quote!(#a + #term)),
                    (Some(a), false) => Some(quote!(#a - #term))
                };

            }

        }
    }

    assignments.into_iter()
    .map(|x| x.unwrap_or_else(|| quote!(B3::Scalar::zero()))) //any empty assignments become 0
    .enumerate() //include the index
    .map(
        //prepend the rhs of the assignment
        |(i, assignment)| {
            let index = Literal::usize_unsuffixed(i);
            quote!( #dest[#index] = MaybeUninit::<B3::Scalar>::new(#assignment); )
        }
    )
    //combine everything into one token stream
    .fold(
        TokenStream::new(),
        |mut tts, x| {tts.extend(x); tts}
    )

}

fn gen_mul_for(rhs:(Ident, Algebra), lhs:(Ident, Algebra), dest:(Ident, Algebra)) -> TokenStream {
    gen_mul_raw(
        rhs.0, lhs.0, dest.0,
        rhs.1.bases(), lhs.1.bases(),
        |b| dest.1.index_of(b), dest.1.elements()
    )
}

fn gen_mul_for_dim(rhs:Ident, lhs:Ident, dest:Ident, n1:usize, n2:usize) -> TokenStream {
    let mut tts = TokenStream::new();

    for r in Algebra::all_src_in_dim(n1) {
        for l in Algebra::all_src_in_dim(n2) {
            for d in r.all_dst(l) {
                let mul = gen_mul_for((rhs.clone(),r), (lhs.clone(),l), (dest.clone(),d));
                tts.extend(quote!(
                    (#r, #l, #d) => {
                        #mul
                        unsafe { B3::assume_init(#dest) }
                    },
                ));
            }
        }
    }

    tts

}

fn expect_ident(tt: Option<TokenTree>) -> Result<Ident, String> {
    match tt {
        Some(TokenTree::Ident(id)) => Ok(id),
        Some(tt) => Err(format!("Expected ident, found '{}'", tt)),
        None => Err(format!("Expected ident")),
    }
}

fn expect_specific_punct(tt: Option<TokenTree>, op: char) -> Result<Punct, String> {
    match tt {
        Some(TokenTree::Punct(p)) if p.as_char()==op => Ok(p),
        Some(tt) => Err(format!("Expected '{}', found '{}'", op, tt)),
        None => Err(format!("Expected '{}'", op)),
    }
}

fn expect_usize(tt: Option<TokenTree>) -> Result<usize, String> {
    match tt {
        Some(TokenTree::Literal(p)) =>
            if let Ok(x) = format!("{}", p).parse() {
                Ok(x)
            } else {
                Err(format!("Expected usize literal, found `{}`", p))
            },
        Some(tt) => Err(format!("Expected usize literal, found '{}'", tt)),
        None => Err(format!("Expected usize literal")),
    }
}

fn expect_nothing(tt: Option<TokenTree>) -> Result<(), String> {
    match tt {
        None => Ok(()),
        Some(tt) => Err(format!("Unexpected '{}'", tt)),
    }
}

fn gen_tables_(tts: TokenStream) -> Result<TokenStream, String> {
    //convert to an iterator
    let mut tts = tts.into_iter();

    //get the rhs, lhs, and dest idents AND check syntax
    let algebra = expect_ident(tts.next())?;
    expect_specific_punct(tts.next(), ',')?;
    let rhs = expect_ident(tts.next())?;
    expect_specific_punct(tts.next(), ',')?;
    let lhs = expect_ident(tts.next())?;
    expect_specific_punct(tts.next(), ',')?;
    let dest = expect_ident(tts.next())?;

    expect_specific_punct(tts.next(), ';')?;
    let default_branch = TokenStream::from_iter(tts);

    // expect_specific_punct(tts.next(), ',')?;
    // let n1 = expect_usize(tts.next())?;
    // expect_specific_punct(tts.next(), ',')?;
    // let n2 = expect_usize(tts.next())?;

    // expect_nothing(tts.next())?;

    //generate tables for dims 0-5
    let mut tts = TokenStream::new();
    for n in 0..=4 {
        tts.extend(gen_mul_for_dim(rhs.clone(), lhs.clone(), dest.clone(), n, n))
    }

    Ok(quote!(
        match #algebra {
            #tts
            _ => {
                #default_branch
            }
        }
    ))

}

#[proc_macro]
pub fn gen_mul(tts: proc_macro::TokenStream) -> proc_macro::TokenStream {
    let tts = TokenStream::from(tts);

    match gen_tables_(tts) {
        Ok(res) => res,
        Err(msg) => {
            let msg_token = Literal::string(&*msg);
            quote!{ compile_error!(#msg_token); }
        }
    }.into()

}
