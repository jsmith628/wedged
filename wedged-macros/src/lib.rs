
extern crate proc_macro;
extern crate proc_macro2;
extern crate quote;
extern crate basis_blade;

use proc_macro2::*;
use basis_blade::*;

// fn gen_mul<'a,I1,I2,F>(
//     rhs:Ident, lhs:Ident, dest:Ident, bases1:I1, bases2:I2, indices:F, count:usize
// ) -> TokenStream
// where
//     I1: Iterator<Item = &'a BasisBlade>,
//     I2: Iterator<Item = &'a BasisBlade>,
//     F: Fn(&'a BasisBlade) -> usize
// {
//
//     let mut assignments: Vec<Option<TokenStream>> = vec![None; count];
//
//     for b1 in bases1 {
//         for b2 in bases2 {
//
//             let b3 = b1 * b2;
//
//
//
//         }
//     }
//
//
//
// }
//
// #[proc_macro]
// pub fn gen_tables(tts: proc_macro::TokenStream) -> proc_macro::TokenStream {
//     tts
// }
