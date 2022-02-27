
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

const N:usize = 5;

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
                let term = quote!( #lhs[#i].ref_mul(&#rhs[#j]) );

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

                let is_even = |x:usize| x&1 == 0;

                for n in 0..=N {
                    for g1 in 0..=n {
                        let a1 = Algebra::Blade(n,g1);
                        for g2 in 0..=n {
                            let a2 = Algebra::Blade(n,g2);

                            let gmax = g1+g2;
                            let gmin = g1.max(g2) - g1.min(g2);

                            for g3 in gmin..=gmax {
                                let a3 = Algebra::Blade(n,g3);

                                //we have general optimizations for these:
                                if g1==0 || g2==0 { continue; }
                                if g3==0 && g1==g2 { continue; }
                                if g3==n && g1+g2==n { continue; }
                                if is_even(g1+g2) != is_even(g3) { continue; }

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
                            let sig_n = n&2 != 0;

                            match (n, g1, g2, g3) {

                                //
                                //First, we have some more general optimizations
                                //obviously, these could definitely be easily covered with the
                                //more specific code-gen, but there doesn't seem to be much of a
                                //difference once all is said and done, we get some
                                //optimizations for higher dimensions, and we get slightly
                                //faster compilation times since we need less code-gen
                                //

                                //scalar multiplication
                                (_, 0, g, g3) if g3==g => {
                                    for i in 0..#dest.elements() {
                                        #dest[i] = MaybeUninit::new(#lhs[0].ref_mul(&#rhs[i]));
                                    }
                                    unsafe { Blade::assume_init(#dest) }
                                },
                                (_, g, 0, g3) if g3==g => {
                                    for i in 0..#dest.elements() {
                                        #dest[i] = MaybeUninit::new(#lhs[i].ref_mul(&#rhs[0]));
                                    }
                                    unsafe { Blade::assume_init(#dest) }
                                },

                                //TODO: optimize for dual without rewriting everything

                                //
                                //The geometric product can only change the grade of the factors
                                //via cancelation of commond basis vectors in the components,
                                //so the output grades are all multiples of two from each other
                                //
                                //Thus, for all other grades, we can immediately set everything to zero
                                (n, g1, g2, g3) if (g1+g2)&1 != g3&1 => {
                                    for i in 0..#dest.elements() {
                                        #dest[i] = MaybeUninit::new(Zero::zero());
                                    }
                                    unsafe { Blade::assume_init(#dest) }
                                },

                                //special case for dot product
                                (n, g1, g2, 0) if g1==g2 => {

                                    let mut dot = T3::zero();
                                    for i in 0..#lhs.elements() {
                                        dot += #lhs[i].ref_mul(&#rhs[i])
                                    }

                                    #dest[0] = MaybeUninit::new(if #lhs.neg_sig() { -dot } else { dot });
                                    unsafe { Blade::assume_init(#dest) }
                                },

                                //special case for dual dot product
                                (n, g1, g2, g3) if g1+g2==g3 && g3==n => {

                                    let sig_g = #lhs.neg_sig();

                                    if g1==g2 {

                                        //here, since this grade is its own dual, we have
                                        //to split the mul into two parts that each are selectively
                                        //negated

                                        let mid = #lhs.elements()/2;

                                        let mut dot1 = T3::zero();
                                        let mut dot2 = T3::zero();

                                        for i in 0..mid { dot1 += #lhs[i].ref_mul(&#rhs[i+mid]); }
                                        for i in 0..mid { dot2 += #lhs[i+mid].ref_mul(&#rhs[i]); }

                                        let dot = dot1 + if sig_n { -dot2 } else { dot2 };
                                        #dest[0] = MaybeUninit::new(if sig_g { -dot } else { dot });


                                    } else {

                                        let mut dot = T3::zero();
                                        for i in 0..#lhs.elements() {
                                            dot += #lhs[i].ref_mul(&#rhs[i])
                                        }

                                        //NOTE: this part is *heavily* based on the basis convention
                                        let sig = sig_g ^ if 2*g1>n { sig_n } else { false };
                                        #dest[0] = MaybeUninit::new(if sig { -dot } else { dot });
                                    }

                                    unsafe { Blade::assume_init(#dest) }


                                },

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
