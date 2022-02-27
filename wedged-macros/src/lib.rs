
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
use self::mul::*;

mod algebra;
mod tokens;
mod mul;

const N:usize = 5;

#[proc_macro]
pub fn gen_mul_optimizations(tts: proc_macro::TokenStream) -> proc_macro::TokenStream {
    unwrap_or_error(gen_mul_optimizations_(TokenStream::from(tts)))
}
