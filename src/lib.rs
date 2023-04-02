//! Use-site metaprogramming inspired by staging
//!
//! This crate lets you run code at compile time to produce the tokens other proc_macros will consume.
//! It is also useful for ad-hoc in place code generation, and for making templates (like Jinja or Mustache for your code).
//! It uses its own simple inner language based on handlers, variables, and a user chosen sigil.
//! The stage separation model of Rust does impose some limitations on what this crate can do.
//!
//! There are two common ways to use this crate. As an end user, it is most likely that you will use the [do_with_in] proc_macro directly.
//! But if you want to make use of parts of the functionality in order to implement these features into your own proc_macro directly,
//! or to implement your own handlers offering extended functionality in the staged language, you'll end up (at this stage) using the reexports from
//! [do_with_in_base], most notably [do_with_in_explicit2].
//!
//! The base handler list is in [genericDefaultHandlers].

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

/// The function used to actually run a stage.
///
/// The tokens in `t` are run, using sigils and so on specified in `c` and variables and handlers specified in `v`.
/// This can be used directly inside a proc_macro to give it the features of [do_with_in]; that proc_macro is in fact
/// essentially a thin wrapper around [do_with_in_internal], which is a configuration parsing wrapper around this.
#[doc(inline)]
pub use do_with_in_base::do_with_in_explicit2;

#[doc(inline)]
pub use do_with_in_base::*;

#[doc(inline)]
pub use do_with_in_internal_macros::do_with_in;


