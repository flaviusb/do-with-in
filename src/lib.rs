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
struct Configuration<Start: StartMarker> where Start: Clone {
  allow_prelude: bool,
  sigil: Sigil,
  rest: Option<TokenStream>,
  _do: PhantomData<Start>,
}

type PeekFn = fn(Cursor) -> bool;

trait StartMarker {
  fn name() -> Option<String>;
  //fn type() -> Self::token;
  type token: Parse;// = syn::token::Do;
  fn tokenp() -> PeekFn;// = syn::token::Do;
  type tokend: Parse + ToString + Clone;
}

impl StartMarker for DoMarker {
  fn name() -> Option<String> {
    None //Some(String::from("do"))
  }
  //fn type() -> Self::token {
  //  return (Token![do])
  //}
  type token = syn::token::Do;
  fn tokenp() -> PeekFn {
    syn::token::Do::peek
  }
  type tokend = syn::Ident;
}

#[derive(Debug,Clone)]
struct DoMarker;

impl<T: StartMarker + Clone> Default for Configuration<T> {
  fn default() -> Self {
    //dbg!("Configuration<T>::default()");
    Configuration { allow_prelude: true, sigil: Sigil::default(), rest: None, _do: PhantomData }
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


impl<T: StartMarker + Clone> Parse for Configuration<T> {
  fn parse(input: ParseStream) -> Result<Self> {
    //dbg!("Start of parsing configuration.");
    let mut base_config: Configuration<T> = Default::default();
    //dbg!("Made base config.");
    while !input.is_empty() {
      //dbg!("Start of while.");
      let mut next: Option<&str> = None;
      let mut foo: String = String::from("");
      if let Some(name) = T::name() {
        if let Ok(it) = input.parse::<T::tokend>() {
          if it.to_string().as_str() == name {
            break;
          }
          foo = it.to_string().clone();
          next = Some(foo.as_str().clone());
        }
      } else if T::tokenp()(input.cursor()) {
          //dbg!("iwhflwhedflowhedfl");
          if let Ok(it) = input.parse::<T::token>() {
            break;
          }
      }
      let mut st: String = String::from("");
      let err_pos = input.fork();
      let new_next = if let Some(it) = next { it } else if !input.is_empty() { st = input.parse::<Ident>().expect("blergh").to_string(); &st } else { break; };
      match new_next {
        "sigil" => {
          //dbg!("sigil found");
          input.parse::<Token![:]>()?;
          if input.peek(Token![$]) {
            input.parse::<Token![$]>()?;
            base_config.sigil = Sigil::Dollar;
          } else if input.peek(Token![%]) {
            input.parse::<Token![%]>()?;
            base_config.sigil = Sigil::Percent;
          } else if input.peek(Token![#]) {
            input.parse::<Token![#]>()?;
            base_config.sigil = Sigil::Hash;
          }
        },
        a => {return Err(err_pos.error(format!("Bad configuration section; found {} when sigil or end of prelude expected", a)));},
      };
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
    //dbg!("End of parsing configuration.");
    Ok(base_config)
  }
}

impl<T: StartMarker + Clone> Configuration<T> {
  fn name(&self) -> Option<String> {
    T::name()
  }
}

#[derive(Clone)]
struct Variables<'a, T: StartMarker + Clone> {
  handlers:    Handlers<'a, T>,
  with_interp: HashMap<String, TokenStream2>,
  no_interp:   HashMap<String, TokenStream2>,
}

impl<'a, T: 'static + StartMarker + Clone> Default for Variables<'a, T> {
  fn default() -> Self {
    Variables { handlers: genericDefaultHandlers::<'a, T>(), with_interp: HashMap::new(), no_interp: HashMap::new() }
  }
}

type Handler<T: StartMarker + Clone> = dyn Fn(Configuration<T>, Variables<T>, TokenStream) -> (Variables<T>, TokenStream);
type Handlers<'a, T: StartMarker + Clone> = HashMap<String, Box<&'a Handler<T>>>;


fn ifHandler<T: StartMarker + Clone>(c: Configuration<T>, v: Variables<T>, t: TokenStream) -> (Variables<T>, TokenStream) {
  (v, quote!{println!("todo");}.into())
}

fn defaultHandlers() -> Handlers<'static, DoMarker> {
  let mut m: HashMap<String, Box<&Handler<DoMarker>>> = HashMap::new();
  m.insert(String::from("if"), Box::new(&ifHandler));
  m
}

fn genericDefaultHandlers<'a, T: 'static + StartMarker + Clone>() -> Handlers<'a, T> {
  let mut m: HashMap<String, Box<&Handler<T>>> = HashMap::new();
  m.insert(String::from("if"), Box::new(&ifHandler));
  m
}



#[proc_macro]
pub fn do_with_in(t: TokenStream) -> TokenStream {
  // Check for configuration first
  match syn::parse::<Configuration<DoMarker>>(t) {
    Ok(it) => {
      let mut configuration = it.clone();
      
      let out = match configuration.clone().rest {
        Some(out) => out,
        None      => TokenStream2::new().into(),
      };
      // For now to make testing possible
      configuration.rest = None;
      do_with_in_explicit(TokenStream2::from(out), configuration, Variables::default())
    },
    Err(it) =>  it.to_compile_error().into()  // we actually want to early exit here, not do: do_with_in_explicit(it.to_compile_error().into(), Configuration::<DoMarker>::default(), defaultHandlers()),
  }
}


fn do_with_in_explicit<'a, T: StartMarker + Clone>(t: TokenStream2, c: Configuration<T>, v: Variables<'a, T>) -> TokenStream {
  let mut output = TokenStream2::new();
  let mut use_vars = v;
  //check for variables to insert
  //check for handlers to run
  //insert token
  let token_char = match c.clone().sigil {
    Sigil::Dollar  => '$',
    Sigil::Percent => '%',
    Sigil::Hash    => '#',
  };
  let mut expecting_variable = false;
  for token in t.into_iter() {
    match &token {
      TokenTree2::Punct(punct_char) if punct_char.spacing() == proc_macro2::Spacing::Alone && punct_char.as_char() == token_char => {
        if expecting_variable {
          expecting_variable = false;
          let out: TokenStream2 = TokenStream2::from(TokenTree2::Punct(punct_char.clone()));
          output.extend(out.into_iter());
        } else {
          expecting_variable = true;
        }
      },
      TokenTree2::Ident(ident) => {
        if expecting_variable {
          expecting_variable = false;
          let var_name = ident.to_string();
          // First we check for no interp, then interp
          if let Some(replace) = use_vars.no_interp.get(&var_name) {
            output.extend(replace.clone().into_iter());
          } else if let Some(replace) = use_vars.with_interp.get(&var_name) {
            output.extend(TokenStream2::from(do_with_in_explicit(replace.clone(), c.clone(), use_vars.clone())));
          }
        } else {
          output.extend(TokenStream2::from(TokenTree2::Ident(ident.clone())).into_iter());
        }
      },
      TokenTree2::Group(group) => {
        if expecting_variable {
          expecting_variable = false;
          // Check whether the handler matches
          let stream = group.stream();
          if !stream.is_empty() {
            let mut iter = stream.clone().into_iter();
            if let Some(TokenTree2::Ident(first)) = iter.next().clone() {
              if let Some(handler) = use_vars.clone().handlers.get(&first.to_string()) {
                let (new_vars, more_output) = handler(c.clone(), use_vars.clone(), TokenStream::from(stream));
                use_vars = new_vars;
                output.extend(TokenStream2::from(more_output));
              }
            }

            //if let Some(handler) = v.handlers.get(
          }
        } else {
          output.extend(TokenStream2::from(TokenTree2::Group(group.clone())));
        }
      },
      a => {
        if expecting_variable {
          expecting_variable = false;
          let out: TokenStream2 = TokenStream2::from(TokenTree2::Punct(proc_macro2::Punct::new(token_char.clone(), proc_macro2::Spacing::Alone)));
          output.extend(out.into_iter());
        }
        output.extend(TokenStream2::from(a.clone()).into_iter());
      },
    }
  }
  output.into()
}

/*
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

//#[test]
//fn conf_test_panic2() {
//  do_with_in!(sigil: % ow2eihf do wiwlkef );
//}
