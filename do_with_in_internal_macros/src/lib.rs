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
    //let t = quote! {
    //  #t_new
    //};
    do_with_in_explicit(c, v, #t_new).into()
  }.into()
}

// has_prelude=
//  true  =>
//  false =>
// postlude_marker=
// default default sigil is $
// default_sigil=
// sigil= // <- this also means you can't write 'sigil' in the prelude
// by default, variables = Variables::default() + any modifications from handlers= and no_interp= and with_interp=, but if variables= is specified then you can't use any of those

#[proc_macro_attribute]
pub fn do_with_in_izer(attr: TokenStream, inner: TokenStream) -> TokenStream {
  let mut has_prelude = true;
  let mut postlude_marker = quote!{DoMarker};
  let default_default = quote!{Sigil::Dollar};
  let mut default_sigil = default_default.clone();
  let mut sigil = default_sigil.clone();
  let a: TokenStream2 = attr.into();
  let b: TokenStream2 = inner.into();
  // default_sigil=, sigil=, has_prelude=, postlude_marker=, 
  let mut b_it = b.into_iter();
  b_it.next(); // Check for 'pub'
  b_it.next(); // Check for 'fn'
  let token = b_it.next();
  if let Some(TokenTree2::Ident(name)) = token.clone() {
    let real_name = proc_macro2::Ident::new(&format!{"{}!",name.to_string()}, proc_macro2::Span::call_site());
    let func_arg_name = match b_it.next() {
      Some(TokenTree2::Group(grp)) => {
        if let Some(TokenTree2::Ident(it)) = grp.stream().into_iter().next() {
          it
        } else {
          return quote!{compile_error!{ "Expected an argument list." }}.into()
        }
      },
      Some(x) => {
        let msg = format!("Expected a function argument list, got {}.", x);
        return quote!{compile_error!{ #msg }}.into();
      },
      None => {
        return quote!{compile_error!{ "Missing function for do_with_in_izer to be applied to." }}.into();
      },
    };
    let mut body = TokenStream2::new();
    body.extend(b_it);
    //let c = ...;
    return quote! {
      #[proc_macro]
      pub fn #real_name(t: TokenStream) -> TokenStream {
        let tt: TokenStream2 = t.into();
        let #func_arg_name = do_with_in_base::do_with_in_explicit(c, v, tt).<TokenStream2>::into();
        #body
      }
    }.into()
  } else {
    let msg = format!("Expected a name for a function, got {:?}.", token);
    return quote!{compile_error!{ #msg }}.into();
  }
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


