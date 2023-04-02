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
/// essentially a thin wrapper around [do_with_in_internal], which is a configuration parsing wrapper around this function. If you are
/// using it this way, you can also change the default variables and handlers which are available by passing in your own `v`.
/// [genericDefaultHandlers] gives a list of the default handlers, and the source of that function shows how to create the handlers;
/// [Variables] implements `Default`, so you can easily get a 'batteries included' version to extend.
#[doc(inline)]
pub use do_with_in_base::do_with_in_explicit2;

#[doc(inline)]
pub use do_with_in_base::*;


/// This is the proc_macro most users of this crate will use.
///
/// There is front matter, which can define the sigil and escaping style. Escaping doesn't actually do anything yet though.
/// Then `do`, then after that is where the metaprogramming can happen.
///
/// In the metaprogramming section, variables are identifiers with a sigil prepended. You can create and assign to them with `let` and `var` handlers.
/// Numbers with a sigil prepended are special variables that can be set inside a handler; you cannot assign to them with `let` or `var`.
/// Brackets with a sigil prepended start a handler invocation; the handler invoked will be the first token inside the brackets, which must be an identifier.
///
/// For example, in the following code the sigil is `$`, `$correction_factor` is a normal variable, `$1`, `$2`, and `$3` are special variables set inside the `blah` handler,
/// and `$(let ...)`, `$(mk ...)` and `$(blah ...)` are all handlers.
///
/// ```rust
/// # use do_with_in_internal_macros::do_with_in;
/// # fn main() {
/// do_with_in!{
///    sigil: $
///    do
///    $(let correction_factor = {(-1)})
///    $(mk blah
///        $1 = $2 + $3 + $correction_factor;)
///    $(blah {let mut d} 3 4)
///    d += 1;
///    let correction_factor = $correction_factor;
///  };
///  assert_eq!(d, 8 + correction_factor);
/// # }
/// ```
///
/// For a table of the currently useful handlers that are available by default, see [genericDefaultHandlers].
#[doc(inline)]
pub use do_with_in_internal_macros::do_with_in;


