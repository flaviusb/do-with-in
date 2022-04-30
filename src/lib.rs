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

#[derive(Debug,Copy,Clone,PartialEq,Eq)]
struct Configuration<Start: StartMarker> {
  allow_prelude: bool,
  sigil: Sigil,
  _do: PhantomData<Start>,
}

trait StartMarker {
  fn name() -> String;
}

impl StartMarker for DoMarker {
  fn name() -> String {
    String::from("do")
  }
}

struct DoMarker;

impl<T: StartMarker> Default for Configuration<T> {
  fn default() -> Self {
    Configuration { allow_prelude: true, ..Default::default() }
  }
}

impl<T: StartMarker> Parse for Configuration<T> {
  fn parse(input: ParseStream) -> Result<Self> {
    let mut base_config: Configuration<T> = Default::default();
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
  let mut configuration: Configuration<DoMarker> = Default::default();
  let start = configuration.name();
  //while(t.peek().toString() != "do") {
    //match t.next().toString() {
    //  ... => 
    //}
  //}
  //do_with_in_explicit(t, configuration)
  t
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
