
extern crate proc_macro;
extern crate proc_macro2;
extern crate quote;
extern crate basis_blade;

use proc_macro2::*;

use self::tokens::*;
use self::versor::*;
use self::bench::*;
use self::mul::*;

mod algebra;
mod tokens;
mod versor;
mod bench;
mod mul;

const N:usize = 4;

#[proc_macro]
pub fn gen_mul_optimizations(tts: proc_macro::TokenStream) -> proc_macro::TokenStream {
    unwrap_or_error(gen_mul_optimizations_(TokenStream::from(tts)))
}

#[proc_macro]
pub fn gen_mul_benches(tts: proc_macro::TokenStream) -> proc_macro::TokenStream {
    unwrap_or_error(gen_mul_benches_(TokenStream::from(tts)))
}

#[proc_macro]
pub fn gen_versor_optimizations(tts: proc_macro::TokenStream) -> proc_macro::TokenStream {
    unwrap_or_error(gen_versor_optimizations_(TokenStream::from(tts)))
}

