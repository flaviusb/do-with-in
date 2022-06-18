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
#[macro_use] use do_with_in_internal_macros::*;


fn variables_to_tokens_that_represent_initialising_it<T: StartMarker + Clone>(v: Variables<T>) -> TokenStream2 {
  todo!()
}

pub fn basicUnquoteSpliceHandler<T: StartMarker + Clone>(c: Configuration<T>, v: Variables<T>, t: TokenStream2) -> (Variables<T>, TokenStream2) {
  let mut out = TokenStream2::new();
  let kv_tok   = variables_to_tokens_that_represent_initialising_it(v.clone());
  // Consume the initial 'unquotesplice'
  let mut tokens = t.into_iter();
  let token = tokens.next();
  if let Some(TokenTree2::Ident(name)) = token.clone() {
    if name.to_string() == "unquotesplice" {
      let token = tokens.next();
      if let Some(TokenTree2::Ident(name)) = token.clone() {
        let ident = TokenTree2::Ident(name);
        out.extend(quote!{
        {
          let k = #kv_tok;
          let c = #c;
          do_with_in_explicit_internal!(#ident)
        }
        });
        (v, out)
      } else {
         let msg = format!("Expected a variable name to start an unquotesplice expression, got {:?}.", token);
         return (v, quote!{compile_error!{ #msg }}.into());
      }
    } else {
      let msg = format!("Expected 'unquotesplice' to absolutely start an unquotesplice expression, got {:?}.", token);
      return (v, quote!{compile_error!{ #msg }}.into());
    }
  } else {
    let msg = format!("Expected 'unquotesplice' to absolutely start a unquotesplice expression, got {:?}.", token);
    return (v, quote!{compile_error!{ #msg }}.into());
  }
}
