
extern crate proc_macro;
extern crate proc_macro2;
extern crate quote;
extern crate basis_blade;


use quote::*;
use proc_macro2::*;
use basis_blade::*;
use std::iter::*;

use self::algebra::*;
use self::tokens::*;

mod algebra;
mod tokens;

const N:usize = 4;

fn gen_mul_raw<'a,I1,I2,F>(
    lhs:Ident, rhs:Ident, dest:Ident, bases1:I1, bases2:I2, index_of:F, count:usize, zero: TokenStream
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
                let term = quote!( #lhs.get(#i).ref_mul(#rhs.get(#j)) );

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
    .map(|x| x.unwrap_or_else(|| zero.clone())) //any empty assignments become 0
    .enumerate() //include the index
    .map(
        //prepend the rhs of the assignment
        |(i, assignment)| {
            let index = Literal::usize_unsuffixed(i);
            quote!( #dest[#index] = MaybeUninit::new(#assignment); )
        }
    )
    //combine everything into one token stream
    .fold(
        TokenStream::new(),
        |mut tts, x| {tts.extend(x); tts}
    )

}

fn gen_mul_for(lhs:(Ident, Algebra), rhs:(Ident, Algebra), dest:(Ident, Algebra), zero:TokenStream) -> TokenStream {
    gen_mul_raw(
        lhs.0, rhs.0, dest.0,
        lhs.1.bases(), rhs.1.bases(),
        |b| dest.1.index_of(b), dest.1.elements(), zero
    )
}

fn gen_mul_for_dim(lhs:Ident, rhs:Ident, dest:Ident, n1:usize, n2:usize) -> TokenStream {
    let mut tts = TokenStream::new();

    for l in Algebra::all_src_in_dim(n1) {
        for r in Algebra::all_src_in_dim(n2) {
            for d in r.all_dst(l) {
                let mul = gen_mul_for(
                    (lhs.clone(),l), (rhs.clone(),r), (dest.clone(),d),
                    quote!(B3::Scalar::zero())
                );
                tts.extend(quote!(
                    (#l, #r, #d) => {
                        #mul
                        unsafe { B3::assume_init(#dest) }
                    },
                ));
            }
        }
    }

    tts

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
    for n in 0..=N {
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
    unwrap_or_error(gen_tables_(TokenStream::from(tts)))
}


fn gen_mul_optimizations_(tts: TokenStream) -> Result<TokenStream, String> {

    //convert to an iterator
    let mut tts = tts.into_iter();

    let lhs = expect_ident(tts.next())?;
    expect_specific_punct(tts.next(), ',')?;
    let lhs_algebra = expect_algebra(tts.next())?.to_string();
    expect_specific_punct(tts.next(), ',')?;

    let rhs = expect_ident(tts.next())?;
    expect_specific_punct(tts.next(), ',')?;
    let rhs_algebra = expect_algebra(tts.next())?.to_string();
    expect_specific_punct(tts.next(), ',')?;

    let shape = expect_ident(tts.next())?;
    expect_specific_punct(tts.next(), ',')?;
    let dest_algebra = expect_algebra(tts.next())?.to_string();

    expect_specific_punct(tts.next(), ';')?;
    let default_branch = TokenStream::from_iter(tts);

    Ok(
        match (&*lhs_algebra, &*rhs_algebra, &*dest_algebra) {

            ("Blade", "Blade", "Blade") => {

                let dest = Ident::new("dest", Span::call_site());
                let mut patterns = TokenStream::new();

                // let is_even = |x:usize| x&1 == 0;

                for n in 0..=N {
                    for g1 in 0..=n {
                        let a1 = Algebra::Blade(n,g1);
                        for g2 in 0..=n {
                            let a2 = Algebra::Blade(n,g2);

                            let gmax = g1+g2;
                            let gmin = g1.max(g2) - g1.min(g2);

                            for g3 in gmin..=gmax {
                                let a3 = Algebra::Blade(n,g3);

                                // if is_even(g1+g2) != is_even(g3) { continue; }

                                //generate the multiplication operation
                                let table = gen_mul_for(
                                    (lhs.clone(), a1), (rhs.clone(), a2), (dest.clone(), a3),
                                    quote!(T3::zero())
                                );

                                //add the pattern
                                patterns.extend(quote!(
                                    (#n, #g1, #g2, #g3) => {
                                        #table
                                        unsafe { Blade::assume_init(#dest) }
                                    }
                                ));

                            }
                        }
                    }
                }

                quote!(
                    {
                        //allocate the destination
                        let mut dest = Blade::<T3,N,G3>::uninit(#shape);

                        //grabe the dims and grades
                        let (n1, n2, n3) = (#lhs.dim(), #rhs.dim(), #shape.0.value());
                        let (g1, g2, g3) = (#lhs.grade(), #rhs.grade(), #shape.1.value());

                        //first, check that the dims are all the same since the optimizations are all
                        //for blades of the same dim
                        if n1==n2 && n2==n3 {

                            let n = n1;
                            match (n, g1, g2, g3) {

                                //special case for dot product
                                // (n, g, g) => {
                                //
                                //     let mut dot = Zero::zero();
                                //     for i in 0..#lhs.elements() {
                                //         dot += #lhs[i].ref_mul(&#rhs[i])
                                //     }
                                //
                                //     if #lhs.neg_sig() { -dot } else { dot }
                                // },

                                //paste in all the generated cases
                                #patterns

                                //the default branch
                                _ => #default_branch

                            }

                        } else {
                            #default_branch
                        }
                    }


                )

            },

            _ => quote!(#default_branch)
        }
    )

}

#[proc_macro]
pub fn gen_mul_optimizations(tts: proc_macro::TokenStream) -> proc_macro::TokenStream {
    unwrap_or_error(gen_mul_optimizations_(TokenStream::from(tts)))
}
