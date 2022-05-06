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
use syn::parse::{Parse, ParseStream, Parser};
use syn::spanned::Spanned;
use syn::{Expr, Ident, Type, Visibility};
use syn::punctuated::Punctuated;
use syn::parenthesized;
use syn::token::Token;

use std::marker::PhantomData;

use std::collections::HashMap;

#[derive(Debug,Copy,Clone,PartialEq,Eq)]
enum Sigil {
  Dollar,
  Percent,
  Hash,
}

impl Default for Sigil {
  fn default() -> Self {
    Sigil::Dollar
  }
}

#[derive(Debug,Clone)]
struct Configuration<Start: StartMarker> {
  allow_prelude: bool,
  sigil: Sigil,
  rest: Option<TokenStream>,
  _do: PhantomData<Start>,
}

trait StartMarker {
  fn name() -> String;
  //fn type() -> Self::token;
  type token: Parse;// = syn::token::Do;
}

impl StartMarker for DoMarker {
  fn name() -> String {
    String::from("do")
  }
  //fn type() -> Self::token {
  //  return (Token![do])
  //}
  type token = syn::token::Do;
}

struct DoMarker;

impl<T: StartMarker> Default for Configuration<T> {
  fn default() -> Self {
    Configuration { allow_prelude: true, ..Default::default() }
  }
}

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


impl<T: StartMarker> Parse for Configuration<T> {
  fn parse(input: ParseStream) -> Result<Self> {
    let mut base_config: Configuration<T> = Default::default();
    while !input.is_empty() {
      if let it = input.parse::<T::token>() {
        break;
      }
      match input.parse::<Ident>()?.to_string().as_str() {
        "sigil" => println!("sigil found"),
        a => println!("found: {}", a),
      }
    }
    let mut fat = TokenStream2::new();
    input.step(|cursor| {
      let mut rest = *cursor;
      while let Some((tt, next)) = rest.token_tree() {
        fat.extend(TokenStream2::from(tt).into_iter());
        rest = next;
      }
      Ok(((), rest))
    });

    base_config.rest = Some(fat.into());
    //while(input.parse
    Ok(base_config)
  }
}

impl<T: StartMarker> Configuration<T> {
  fn name(&self) -> String {
    T::name()
  }
}

#[derive(Debug,Copy,Clone,PartialEq,Eq)]
struct Variables {}

type Handler<T: StartMarker> = dyn Fn(Configuration<T>, Variables, TokenStream) -> (Variables, TokenStream);
type Handlers<T: StartMarker> = HashMap<String, Box<Handler<T>>>;


fn ifHandler<T: StartMarker>(c: Configuration<T>, v: Variables, t: TokenStream) -> (Variables, TokenStream) {
  (v, t)
}

fn defaultHandlers() -> Handlers<DoMarker> {
  let mut m: HashMap<String, Box<Handler<DoMarker>>> = HashMap::new();
  m.insert(String::from("if"), Box::new(ifHandler));
  m
}



#[proc_macro]
pub fn do_with_in(t: TokenStream) -> TokenStream {
  // Check for configuration first
  let mut configuration = syn::parse::<Configuration<DoMarker>>(t).unwrap();
  
  //while(t.peek().toString() != "do") {
    //match t.next().toString() {
    //  ... => 
    //}
  //}
  //do_with_in_explicit(t, configuration)
  match configuration.rest {
    Some(out) => out,
    None      => TokenStream2::new().into(),
  }
}

/*
fn do_with_in_explicit(t: TokenStream, c: Configuration) -> TokenStream {
  ...
}

fn with_maker(args: ArgList, body: Body) -> Handler {
  |c: Configuration, v: Variables, t: TokenStream| {
    // First match on the args
    // Then put substitutions in the body tokenstream
    (v, t)
  }
}

#[proc_macro_attribute]
fn do_with_in_izer(args: TokenStream, body: TokenStream) -> TokenStream {
  let mut configuration = defaultConfiguration();
  // Update configuration from args
  let new_body = quote!(
    let new_args = do_with_in_explicit(t);
    $body
  }
  new_body
}

*/
#[cfg(test)]
mod tests {
    #[test]
    fn it_works() {
        let result = 2 + 2;
        assert_eq!(result, 4);
    }
}
