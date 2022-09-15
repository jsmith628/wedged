
use quote::*;
use proc_macro2::*;
use std::iter::*;

use crate::tokens::*;
use crate::algebra::*;

const BLADE_NAMES: &[&str] = &[
    "scalar",
    "vec",
    "bivec",
    "trivec",
    "quadvec",
    "pentvec",
    "hexvec"
];

fn gen_bench(name: Ident, ty1: &TokenStream, ty2: &TokenStream, op: Punct) -> TokenStream {

    quote! {
        #[bench]
        fn #name(b: &mut test::Bencher) {
            b.iter(
                ||
                // for _ in 0..1000
                {
                    test::black_box(
                        test::black_box(<#ty1 as Default>::default()) #op 
                        test::black_box(<#ty2 as Default>::default())
                    );
                }
            )
        }
    }
}

pub fn gen_mul_benches_(tts: TokenStream) -> Result<TokenStream, String> {

    //convert to an iterator
    let mut tts = tts.into_iter();

    //get how many dims to gen benchmarks for
    let max_dim = expect_usize(tts.next())?;
    expect_specific_punct(tts.next(), ';')?;

    //get what scalars to use in the benchmarks (must impl Default)
    let types = parse_csv(TokenStream::from_iter(tts))?;

    let mut benches = TokenStream::new();
    let span = Span::call_site();
    for n in 0..=max_dim {

        //blades
        for g1 in 0..=n {
            for g2 in g1..=n {
                for scalar in &types {

                    let ty1 = Algebra::Blade(n, g1).to_ty_tokens(scalar.clone());
                    let ty2 = Algebra::Blade(n, g1).to_ty_tokens(scalar.clone());

                    //for wedge
                    let name = format!("wedge_{}_{}_{}D_{}", BLADE_NAMES[g1], BLADE_NAMES[g2], n, scalar);
                    benches.extend(
                        gen_bench(Ident::new(&*name, span), &ty1, &ty2, Punct::new('^', Spacing::Alone))
                    );

                    //for dot
                    let name = format!("dot_{}_{}_{}D_{}", BLADE_NAMES[g1], BLADE_NAMES[g2], n, scalar);
                    benches.extend(
                        gen_bench(Ident::new(&*name, span), &ty1, &ty2, Punct::new('%', Spacing::Alone))
                    );

                }
            }
        }

        //the other subalgebras
        for scalar in &types {
            let even = Algebra::Even(n).to_ty_tokens(scalar.clone());
            let odd = Algebra::Odd(n).to_ty_tokens(scalar.clone());
            let full = Algebra::Full(n).to_ty_tokens(scalar.clone());

            let name = format!("mul_even_even_{}D_{}", n, scalar);
            benches.extend(
                gen_bench(Ident::new(&*name, span), &even, &even, Punct::new('*', Spacing::Alone))
            );

            let name = format!("mul_odd_odd_{}D_{}", n, scalar);
            benches.extend(
                gen_bench(Ident::new(&*name, span), &odd, &odd, Punct::new('*', Spacing::Alone))
            );

            let name = format!("mul_even_odd_{}D_{}", n, scalar);
            benches.extend(
                gen_bench(Ident::new(&*name, span), &even, &odd, Punct::new('*', Spacing::Alone))
            );

            let name = format!("mul_multivector_{}D_{}", n, scalar);
            benches.extend(
                gen_bench(Ident::new(&*name, span), &full, &full, Punct::new('*', Spacing::Alone))
            );
        }

    }

    return Ok(benches);


}
