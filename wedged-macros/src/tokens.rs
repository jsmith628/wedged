
use proc_macro2::*;
use quote::*;

pub fn expect_ident(tt: Option<TokenTree>) -> Result<Ident, String> {
    match tt {
        Some(TokenTree::Ident(id)) => Ok(id),
        Some(tt) => Err(format!("Expected ident, found '{}'", tt)),
        None => Err(format!("Expected ident")),
    }
}

pub fn expect_specific_punct(tt: Option<TokenTree>, op: char) -> Result<Punct, String> {
    match tt {
        Some(TokenTree::Punct(p)) if p.as_char()==op => Ok(p),
        Some(tt) => Err(format!("Expected '{}', found '{}'", op, tt)),
        None => Err(format!("Expected '{}'", op)),
    }
}

#[allow(dead_code)]
pub fn expect_usize(tt: Option<TokenTree>) -> Result<usize, String> {
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

#[allow(dead_code)]
pub fn expect_nothing(tt: Option<TokenTree>) -> Result<(), String> {
    match tt {
        None => Ok(()),
        Some(tt) => Err(format!("Unexpected '{}'", tt)),
    }
}


pub fn unwrap_or_error(res: Result<TokenStream, String>) -> proc_macro::TokenStream {

    match res {

        //if ok, we're good to go
        Ok(tts) => tts,

        //else, we display the error message as a compile_error!() call
        //TODO: once `Diagnostic`s are stabilized, those should be used instead
        Err(msg) => {
            let msg_token = Literal::string(&*msg);
            quote!{ compile_error!(#msg_token); }
        }

    }.into()

}
