extern crate do_with_in_base;
extern crate proc_macro;
extern crate syn;
#[macro_use] extern crate quote;
extern crate proc_macro2;

use proc_macro::{TokenStream, TokenTree};
use proc_macro2::TokenTree as TokenTree2;
use proc_macro2::TokenStream as TokenStream2;
use quote::{quote, quote_spanned};
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

#[test]
fn missing_variable() {
  let c = Configuration::<DoMarker>::default();
  let v = Variables::<DoMarker>::default();
  let cmpl = format!("{:?}", do_with_in_explicit(quote!{$a}, c, v));
  let cmpr = format!("{:?}", quote!{compile_error!{"No such variable: a defined."}});
  assert_eq!(cmpl, cmpr);
}

use std::str::FromStr;
use std::io;
use std::io::prelude::*;
use std::path::{Path, PathBuf};
use std::ffi::OsStr;
use std::fs::File;

#[test]
fn missing_variable_inside_import() {
  let thing = "tests";
  let mut file = Path::new(&thing).to_path_buf();
  file.push("missing_variable.$");
  let path = file.into_os_string();
  let mut c = Configuration::<DoMarker>::default();
  c.file = Some(file!().to_string());
  let v = Variables::<DoMarker>::default();
  let cmpl = format!("{}", do_with_in_explicit(quote!{$(import Base "tests" "missing_variable.$")}, c, v));
  let msg = format!("Problem encountered inside import {:?}.", path);
  let cmpr = format!("{}", quote!{compile_error!{"No such variable: b defined."} compile_error!{ #msg }});
  assert_eq!(cmpl, cmpr);
}
