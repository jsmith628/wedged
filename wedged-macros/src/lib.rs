
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

fn gen_mul_raw<'a,I1,I2,F>(
    lhs:Ident, rhs:Ident, dest:Ident, bases1:I1, bases2:I2, index_of:F, count:usize
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

fn gen_mul_for(lhs:(Ident, Algebra), rhs:(Ident, Algebra), dest:(Ident, Algebra)) -> TokenStream {
    gen_mul_raw(
        lhs.0, rhs.0, dest.0,
        lhs.1.bases(), rhs.1.bases(),
        |b| dest.1.index_of(b), dest.1.elements()
    )
}

fn gen_mul_for_dim(lhs:Ident, rhs:Ident, dest:Ident, n1:usize, n2:usize) -> TokenStream {
    let mut tts = TokenStream::new();

    for l in Algebra::all_src_in_dim(n1) {
        for r in Algebra::all_src_in_dim(n2) {
            for d in r.all_dst(l) {
                let mul = gen_mul_for((lhs.clone(),l), (rhs.clone(),r), (dest.clone(),d));
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
    unwrap_or_error(gen_tables_(TokenStream::from(tts)))
}


// fn gen_mul_optimizations_(tts: TokenStream) -> Result<TokenStream, String> {
//
//     let lhs = expect_ident(tts.next())?;
//     expect_specific_punct(tts.next(), ',')?;
//     let rhs = expect_ident(tts.next())?;
//     expect_specific_punct(tts.next(), ',')?;
//     let dest = expect_ident(tts.next())?;
//
//     Ok(TokenStream::new())
// }
//
// #[proc_macro]
// pub fn gen_mul_optimizations(tts: proc_macro::TokenStream) -> proc_macro::TokenStream {
//     unwrap_or_error(gen_mul_optimizations_(TokenStream::from(tts)))
// }
