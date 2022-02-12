
extern crate proc_macro;
extern crate proc_macro2;
extern crate quote;
extern crate basis_blade;

use quote::*;
use proc_macro2::*;
use basis_blade::*;

// #[derive(Clone, Copy, hash)]
// pub enum Algebra {
//     Blade(usize, usize),
//     Even(usize, usize),
//     Odd(usize, usize),
//     Full(usize, usize)
// }
//
// impl Algebra {
//
//     pub fn bases(self) ->
//
// }


fn gen_mul<'a,I1,I2,F>(
    rhs:Ident, lhs:Ident, dest:Ident, bases1:I1, bases2:I2, index_of:F, count:usize
) -> TokenStream
where
    I1: Iterator<Item = &'a BasisBlade>,
    I2: Iterator<Item = &'a BasisBlade>+Clone,
    F: Fn(BasisBlade) -> usize
{

    //the list of assignments to each component of the destination value
    let mut assignments: Vec<Option<TokenStream>> = vec![None; count];

    //loop over every pair of basis vectors
    for b1 in bases1 {
        for b2 in bases2.clone() {

            //find the basis of the result and its index
            let b3 = b1 * b2;
            let index = index_of(b3);

            //tokens for multiplying the components of the rhs and lhs
            let term = quote!(  #rhs.ref_mul(&#lhs) );

            //add this term to the corresponding coordinate
            assignments[index] = match &assignments[index] {
                None => Some(term),
                Some(a) => Some(quote!(#(#a) + #(#term)))
            };



        }
    }

    assignments.into_iter()
    .map(|x| x.unwrap_or_else(|| quote!(T::zero()))) //any empty assignments become 0
    .enumerate() //include the index
    .map(
        //prepend the rhs of the assignment
        |(i, assignment)| {
            let index = Literal::usize_unsuffixed(i);
            quote!( #dest[#index] = #(#assignment); )
        }
    )
    //combine everything into one token stream
    .fold(
        TokenStream::new(),
        |mut tts, x| {tts.extend(x); tts}
    )

}

#[proc_macro]
pub fn gen_tables(tts: proc_macro::TokenStream) -> proc_macro::TokenStream {
    tts
}
