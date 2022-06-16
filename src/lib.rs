extern crate proc_macro;
extern crate syn;
#[macro_use] extern crate quote;
extern crate proc_macro2;

use proc_macro::{TokenStream, TokenTree};
use proc_macro2::TokenTree as TokenTree2;
use proc_macro2::TokenStream as TokenStream2;
use quote::quote;
use quote::ToTokens;
use syn::{parse, Attribute, PathSegment, Result, Token};
use syn::parse::{Parse, ParseStream, Parser, Peek};
use syn::spanned::Spanned;
use syn::{Expr, Ident, Type, Visibility};
use syn::punctuated::Punctuated;
use syn::parenthesized;
use syn::token::Token;
use syn::buffer::Cursor;

use std::marker::PhantomData;

use std::collections::HashMap;
use std::fmt::format;

use do_with_in_base::*;

struct Fatuous {
  fat: TokenStream,
}

impl Parse for Fatuous {
  fn parse(input: ParseStream) -> Result<Self> {
    let mut fat = TokenStream2::new();
    input.step(|cursor| {
      let mut rest = *cursor;
      while let Some((tt, next)) = rest.token_tree() {
        fat.extend(TokenStream2::from(tt).into_iter());
        rest = next;
      }
      Ok(((), rest))
    });
    Ok(Fatuous { fat: fat.into() })
  }
}




#[proc_macro]
pub fn do_with_in(t: TokenStream) -> TokenStream {
  do_with_in_internal(t.into()).into()
}


#[proc_macro]
pub fn do_with_in_explicit_internal(t: TokenStream) -> TokenStream {
  let t_new: TokenStream2 = t.into();
  quote! {
    do_with_in_explicit(c, v, #t_new).into()
  }.into()
}

/*

make output tokenstream2
Make HashMap ToTokens if K, V are ToTokens
Make fn thing ToTokens through... ways?
add them to output as c=..., v=...
add ⌜quote!{do_with_in_explicit_internal!(#ident)}

let out = TokenStream2::new();
let kv_tok   = k.to_tokens();
let conf_tok = c.to_tokens();
out.extend(quote!{
  {
    let k = #kv_tok;
    let c = #conf_tok; 
    do_with_in_explicit_internal!(#ident)
  }
});
out


 */
