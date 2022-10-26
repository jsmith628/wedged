use quote::*;
use proc_macro2::*;
use std::iter::*;

use crate::tokens::*;
use crate::algebra::*;
use crate::N;

pub fn gen_versor_mul_table(
    v:(Ident, Algebra), a:(Ident, Algebra), dest:(Ident, Algebra), zero:TokenStream
) -> TokenStream {

    use std::collections::HashMap;

    #[derive(Copy, Clone, PartialEq, Eq, Hash)]
    struct Term(usize, usize, usize);

    let mut assignments: Vec<HashMap<Term,i32>> = vec![HashMap::new(); dest.1.elements()];
    let versor = v.0;
    let object = a.0;


    let odd = v.1.odd();

    for (i, vb1) in v.1.bases() {
        for (j, vb2) in v.1.bases() {
            for (k, b) in a.1.bases() {
                

                let b = if odd { b.involute() } else { b };
                let dest_b = vb1 * b / vb2;

                if let Some((index, neg)) = dest.1.index_of(dest_b) {

                    //the key for the term so we can keep track of the coefficient
                    let term = Term(i.min(j), i.max(j), k);

                    match (assignments[index].get_mut(&term), neg) {
                        (None, true) => {assignments[index].insert(term, 1);},
                        (None, false) => {assignments[index].insert(term, -1);},
                        (Some(a), true) => *a += 1,
                        (Some(a), false) => *a -= 1
                    }
    
                }

            }
        }
    }

    let dest = dest.0;
    let mut tts = TokenStream::new();
    for (i, assignment) in assignments.into_iter().enumerate() {

        let mut expr = TokenStream::new();
        let mut first = true;

        for (Term(j,k,l), coeff) in assignment {

            //we sadly can't multiply by ints because of the generics
            //so we have to just use repeated addition
            for _ in 0..(coeff.abs()) {
                if coeff < 0 {
                    expr.extend(quote!(-));
                } else if !first && coeff > 0 {
                    expr.extend(quote!(+));
                }
    
                expr.extend(
                    quote!(
                        (#versor[#j].ref_mul(&#object[#l]) * &#versor[#k])
                    )
                );
    
                first = false;
            }            
        }

        if expr.is_empty() {
            expr = zero.clone()
        }

        tts.extend(
            quote!( #dest[#i] = ::std::mem::MaybeUninit::new(#expr); )
        );


    }

    tts

}

pub fn gen_versor_mul(
    versor: Ident, _versor_ty: Ident, versor_alg: AlgebraKind,
    object: Ident, object_ty: Ident, object_alg: AlgebraKind,
    default_branch: TokenStream
) -> TokenStream {

    let v = versor;
    let x = object;
    let dest = Ident::new("dest", Span::call_site());
    let output = object_ty;

    let mut patterns = vec![];

    for n in 0..=N {
        for a1 in versor_alg.iter_at(n) {
            for a2 in object_alg.iter_at(n) {
                
                let p1 = match a1 {
                    Algebra::Blade(_, g) => quote!(, #g),
                    _ => quote!(),
                };

                let p2 = match a2 {
                    Algebra::Blade(_, g) => quote!(, #g),
                    _ => quote!(),
                };

                let table = gen_versor_mul_table(
                    (v.clone(),a1), (x.clone(),a2), (dest.clone(), a2),
                    quote!(U::zero())
                );

                patterns.push(
                    quote!(
                        (#n #p1 #p2) => {
                            #table
                            unsafe { #output::assume_init(#dest) }
                        },
                    )
                );                

            }
        }
    }

    let p1 = match versor_alg {
        AlgebraKind::Blade => quote!(, #v.grade()),
        _ => quote!(),
    };

    let p2 = match object_alg {
        AlgebraKind::Blade => quote!(, #x.grade()),
        _ => quote!(),
    };

    let out_ty = match object_alg {
        AlgebraKind::Blade => quote!(#output::<U,_,_>),
        _ => quote!(#output::<U,_>),
    };

    quote!{{

        let shape = #x.shape();
        let mut #dest = #out_ty::uninit(shape);
        
        if #v.dim() == #x.dim() {
            match (#v.dim() #p1 #p2) {
                #(#patterns)*
                _ => #default_branch
            }
        } else {
            #default_branch
        }

    }}


}

pub fn gen_versor_optimizations_(tts: TokenStream) -> Result<TokenStream, String> {
    
    let mut tts = tts.into_iter();

    let versor = expect_ident(tts.next())?;
    expect_specific_punct(tts.next(), ',')?;
    let versor_ty = expect_ident(tts.next())?;
    let versor_alg = AlgebraKind::of(&versor_ty)?;
    expect_specific_punct(tts.next(), ',')?;

    let obj = expect_ident(tts.next())?;
    expect_specific_punct(tts.next(), ',')?;
    let obj_ty = expect_ident(tts.next())?;
    let obj_alg = AlgebraKind::of(&obj_ty)?;
    expect_specific_punct(tts.next(), ';')?;

    let default_branch = TokenStream::from_iter(tts);

    Ok(gen_versor_mul(
        versor, versor_ty, versor_alg, obj, obj_ty, obj_alg, default_branch
    ))
    
}