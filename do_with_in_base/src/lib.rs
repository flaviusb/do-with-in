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
pub enum Sigil {
  Dollar,
  Percent,
  Hash,
  Tilde,
}
use std::fmt;
impl fmt::Display for Sigil {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    let out = match self {
      Sigil::Dollar  => "$",
      Sigil::Percent => "%",
      Sigil::Hash    => "#",
      Sigil::Tilde   => "~",
    };
    write!(f, "{}", out)
  }
}
use quote::TokenStreamExt;
impl ToTokens for Sigil {
  fn to_tokens(&self, tokens: &mut TokenStream2) {
    tokens.extend(match self {
      Sigil::Dollar  => quote!{do_with_in_base::Sigil::Dollar},  //Ident::new("do_with_in_base::Sigil::Dollar", proc_macro2::Span::call_site()),
      Sigil::Percent => quote!{do_with_in_base::Sigil::Percent}, //Ident::new("do_with_in_base::Sigil::Percent", proc_macro2::Span::call_site()),
      Sigil::Hash    => quote!{do_with_in_base::Sigil::Hash},    //Ident::new("do_with_in_base::Sigil::Hash", proc_macro2::Span::call_site()),
      Sigil::Tilde   => quote!{do_with_in_base::Sigil::Tilde},   //Ident::new("do_with_in_base::Sigil::Tilde", proc_macro2::Span::call_site()),
    });
  }
}

impl Default for Sigil {
  fn default() -> Self {
    Sigil::Dollar
  }
}

#[derive(Debug,Copy,Clone,PartialEq,Eq)]
pub enum Escaping {
  None,
  Backslash,
  Double,
}

impl ToTokens for Escaping {
  fn to_tokens(&self, tokens: &mut TokenStream2) {
    tokens.extend(match self {
      Escaping::None      => quote!{do_with_in_base::Escaping::None},
      Escaping::Backslash => quote!{do_with_in_base::Escaping::Backslash},
      Escaping::Double    => quote!{do_with_in_base::Escaping::Double},
    });
  }
}

impl Default for Escaping {
  fn default() -> Self {
    Escaping::Double
  }
}

#[derive(Debug,Clone)]
pub struct Configuration<Start: StartMarker> where Start: Clone {
  pub allow_prelude: bool,
  pub sigil: Sigil,
  pub escaping_style: Escaping,
  pub rest: Option<TokenStream2>,
  _do: PhantomData<Start>,
}

impl<T> ToTokens for Configuration<T> where T: StartMarker + Clone {
  fn to_tokens(&self, tokens: &mut TokenStream2) {
    let c = self.clone();
    let p = c.allow_prelude;
    let s = c.sigil;
    let e = c.escaping_style;
    let rest = match c.rest {
      Some(x) => quote! { Some(quote!{#x}) },
      None    => quote! { None },
    };
    let t = T::token_token();

    tokens.extend(quote!{
      Configuration::<#t> {
        allow_prelude: #p,
        sigil: #s,
        escaping_style: #e,
        rest: #rest,
        _do: PhantomData,
      }
    });
  }
}

macro_rules! check_token {
  ($y:pat, $z:expr, $err:literal, $v:expr, $err2: literal) => {
    if let $y = $z {
      if $v {
        ()
      } else {
        return Err($err2);
      }
    } else {
      return Err($err);
    }
  };
}

macro_rules! check_token_ret {
  ($vars: expr, $y:pat, $z:expr, $err:literal, $v:expr, $err2: literal) => {
    if let $y = $z {
      if $v {
        ()
      } else {
        //let msg = $err2;
        return ($vars, quote!{compile_error!{ $err2 }}.into());
      }
    } else {
        //let msg = $err;
        return ($vars, quote!{compile_error!{ $err }}.into());
    }
  };
}

#[derive(Debug,Clone)]
struct ConfigurationChunks {
  allow_prelude: Option<bool>,
  sigil: Option<Sigil>,
  escaping_style: Option<Escaping>,
  rest: Option<Option<TokenStream2>>,
  marker: Vec<syn::Ident>,
}

enum Chunks {
  AllowPrelude,
  Sigil,
  EscapingStyle,
  Rest,
  Do,
}

// ~, or Tilde, or Sigil::Tilde, or do_with_in_base::Sigil::Tilde
enum GetSigil {
  ExpectingColonsThenSigil,
  ExpectingColonThenSigil,
  ExpectingSigil,
  ExpectingColonsThenEnd,
  ExpectingColonThenEnd,
  ExpectingEnd,
}

// Double, or Expecting::Double, or do_with_in_base::Expecting::Double
enum GetEscaping {
  ExpectingColonsThenEscaping,
  ExpectingColonThenEscaping,
  ExpectingEscaping,
  ExpectingColonsThenEnd,
  ExpectingColonThenEnd,
  ExpectingEnd,
}

enum GetChunk {
  NothingYet,
  ChunkType(Chunks),
  Equals(Chunks),
  Sigil(GetSigil), //We get the first part of sigil from Equals(Sigil), then pass to the relevant kind of Sigil(GetSigil)
  Escaping(GetEscaping),
  Some, //Some should only be present when we are expecting a TokenStream2 after Equals(Rest) found a 'Some'
}

macro_rules! unwrap_struct {
  ($name:literal, $iter:ident, $part:ident,  $get_type_bits:stmt) => {
    {
      check_token!(Some(TokenTree2::Ident(conf)), $iter.next(), "Expected struct name", conf.to_string() == $name, "Expected struct name");
      check_token!(Some(TokenTree2::Punct(sc)), $iter.next(), "Expected ':' (first part of ::).", sc.as_char() == ':', "Expected ':' (first part of ::).");
      check_token!(Some(TokenTree2::Punct(sc)), $iter.next(), "Expected ':' (second part of ::).", sc.as_char() == ':', "Expected ':' (second part of ::).");
      check_token!(Some(TokenTree2::Punct(lt)), $iter.next(), "Expected '<'", lt.as_char() == '<', "Expected '<'.");
      // This bit is a bit tricky, as we expect ⌜ident (colon colon ident)*⌝
      let mut cont = true;
      let mut at_all = false;
      let mut next: Option<TokenTree2> = $iter.next();
      while cont {
        if let Some(TokenTree2::Ident($part)) = next.clone() {
          $get_type_bits;
          at_all = true;
          next = $iter.next();
          match next {
            Some(TokenTree2::Punct(s)) if s.as_char() == ':' => {
              check_token!(Some(TokenTree2::Punct(sc)), $iter.next(), "Expected ':' (second part of ::), for type.", sc.as_char() == ':', "Expected ':' (second part of ::), for type.");
              next = $iter.next();
            },
            x => {
              next = x;
              cont = false;
            },
          }
        } else if at_all {
          cont = false;
        } else {
          return Err("Expected a part of a type.");
        }
      }
      check_token!(Some(TokenTree2::Punct(gt)), next, "Expected '>'", gt.as_char() == '>', "Expected '>'.");
      let inner = if let Some(TokenTree2::Group(group)) = $iter.next() {
        group.stream()
      } else {
        return Err("No group when one was expected.");
      };
      inner
    }
  }
}

impl<T> TryFrom<TokenStream2> for Configuration<T> where T: StartMarker + Clone {
  type Error = &'static str;
  fn try_from(value: TokenStream2) -> std::result::Result<Self, Self::Error> {
    let mut cc = ConfigurationChunks { allow_prelude: None, sigil: None, escaping_style: None, rest: None, marker: Vec::new(), };
    let mut iter = value.into_iter();
    let inner = unwrap_struct!("Configuration", iter, x, cc.marker.push(x));
    let mut progress = GetChunk::NothingYet;
    for thing in inner.into_iter() {
      match progress {
        GetChunk::NothingYet => {
          match thing {
            TokenTree2::Ident(name) => {
              progress = GetChunk::ChunkType(match name.to_string().as_str() {
                "allow_prelude"  => Chunks::AllowPrelude,
                "sigil"          => Chunks::Sigil,
                "escaping_style" => Chunks::EscapingStyle,
                "rest"           => Chunks::Rest,
                "_do"            => Chunks::Do,
                x                => return Err("Expecting allow_prelude, sigil, escaping_style, or rest."),
              });
            },
            TokenTree2::Punct(comma) if comma.as_char() == ',' => {
              progress = GetChunk::NothingYet; // We stay at this point in the state machine
            },
            _ => {
              return Err("Expecting allow_prelude, sigil, escaping_style, or rest.");
            },
          }
        },
        GetChunk::ChunkType(chunk) => {
          check_token!(TokenTree2::Punct(eq), thing, "Expected ':'", eq.as_char() == ':', "Expected ':'.");
          progress = GetChunk::Equals(chunk);
        },
        GetChunk::Equals(Chunks::AllowPrelude) => {
          if let TokenTree2::Ident(it) = thing {
            cc.allow_prelude = Some(match it.to_string().as_str() {
              "true"  => true,
              "false" => false,
              _       => return Err("Expected 'true' or 'false'."),
            });
            progress = GetChunk::NothingYet;
          } else {
            return Err("Expected 'true' or 'false'");
          }
        },
        GetChunk::Equals(Chunks::Sigil) => {
          match thing {
            TokenTree2::Punct(it) => {
              cc.sigil = Some(match it.as_char() {
                '$' => Sigil::Dollar,
                '~' => Sigil::Tilde,
                '%' => Sigil::Percent,
                '#' => Sigil::Hash,
                _ => return Err("Expected $, %, #, or ~."),
              });
              progress = GetChunk::NothingYet;
            },
            TokenTree2::Ident(it) => {
              match it.to_string().as_str() {
                "Tilde" => {
                  cc.sigil = Some(Sigil::Tilde);
                  progress = GetChunk::NothingYet;
                },
                "Hash"  => {
                  cc.sigil = Some(Sigil::Hash);
                  progress = GetChunk::NothingYet;
                },
                "Dollar" => {
                  cc.sigil = Some(Sigil::Dollar);
                  progress = GetChunk::NothingYet;
                },
                "Percent" => {
                  cc.sigil = Some(Sigil::Percent);
                  progress = GetChunk::NothingYet;
                },
                "Sigil" => {
                  progress = GetChunk::Sigil(GetSigil::ExpectingColonsThenEnd);
                },
                "do_with_in_base" => {
                  progress = GetChunk::Sigil(GetSigil::ExpectingColonsThenSigil);
                },
                _ => return Err("Expected $, %, #, ~, Sigil::..., or do_with_in_base::Sigil::..."),
              }
            },
            _ => {
              return Err("Expected $, %, #, ~, Sigil::..., or do_with_in_base::Sigil::...");
            },
          };
        },
        GetChunk::Equals(Chunks::EscapingStyle) => {
          match thing {
            TokenTree2::Ident(it) => {
              match it.to_string().as_str() {
                "None"      => {
                  cc.escaping_style = Some(Escaping::None);
                  progress = GetChunk::NothingYet;
                },
                "Double"    => {
                  cc.escaping_style = Some(Escaping::Double);
                  progress = GetChunk::NothingYet;
                },
                "Backslash" => {
                  cc.escaping_style = Some(Escaping::Backslash);
                  progress = GetChunk::NothingYet;
                },
                "Escaping"  => {
                  progress = GetChunk::Escaping(GetEscaping::ExpectingColonsThenEnd);
                },
                "do_with_in_base" => {
                  progress = GetChunk::Escaping(GetEscaping::ExpectingColonsThenEscaping);
                },
                _ => return Err("Expected do_with_in_base, Escaping, None, Double, or Backslash"),
              }
            },
            x => return Err("Expected a chunk escaping style."),
          };
        },
        GetChunk::Equals(Chunks::Rest) => {
          match thing {
            TokenTree2::Ident(it) => {
              match it.to_string().as_str() {
                "Some" => progress = GetChunk::Some,
                "None" => {
                  cc.rest = Some(None);
                  progress = GetChunk::NothingYet;
                },
                _ => {
                  return Err("Expected Some(...) or None.");
                },
              }
            },
            _ => {
              return Err("Expected Some(...) or None.");
            }
          }
        },
        GetChunk::Equals(Chunks::Do) => {
          check_token!(TokenTree2::Ident(doit), thing, "Expected 'PhantomData'.", doit.to_string() == "PhantomData", "Expected 'PhantomData'.");
          progress = GetChunk::NothingYet;
        },
        GetChunk::Sigil(GetSigil::ExpectingColonsThenSigil) => {
          check_token!(TokenTree2::Punct(sc), thing, "Expected ':' (first part of ::).", sc.as_char() == ':', "Expected ':' (first part of ::).");
          progress = GetChunk::Sigil(GetSigil::ExpectingColonThenSigil);
        },
        GetChunk::Sigil(GetSigil::ExpectingColonThenSigil) => {
          check_token!(TokenTree2::Punct(sc), thing, "Expected ':' (second part of ::).", sc.as_char() == ':', "Expected ':' (second part of ::).");
          progress = GetChunk::Sigil(GetSigil::ExpectingSigil);
        },
        GetChunk::Sigil(GetSigil::ExpectingSigil) => {
          check_token!(TokenTree2::Ident(id), thing, "Expected 'Sigil'.", id.to_string() == "Sigil", "Expected 'Sigil'.");
          progress = GetChunk::Sigil(GetSigil::ExpectingColonsThenEnd);
        },
        GetChunk::Sigil(GetSigil::ExpectingColonsThenEnd) => {
          check_token!(TokenTree2::Punct(sc), thing, "Expected ':' (first part of ::).", sc.as_char() == ':', "Expected ':' (first part of ::).");
          progress = GetChunk::Sigil(GetSigil::ExpectingColonThenEnd);
        },
        GetChunk::Sigil(GetSigil::ExpectingColonThenEnd) => {
          check_token!(TokenTree2::Punct(sc), thing, "Expected ':' (second part of ::).", sc.as_char() == ':', "Expected ':' (second part of ::).");
          progress = GetChunk::Sigil(GetSigil::ExpectingEnd);
        },
        GetChunk::Sigil(GetSigil::ExpectingEnd) => {
          cc.sigil = match thing.to_string().as_str() {
            "Tilde" => {
              Some(Sigil::Tilde)
            },
            "Hash"  => {
              Some(Sigil::Hash)
            },
            "Dollar" => {
              Some(Sigil::Dollar)
            },
            "Percent" => {
              Some(Sigil::Percent)
            },
            _ => {
              return Err("Expecting Tilde, Hash, Dollar, or Percent.");
            },
          };
          progress = GetChunk::NothingYet;
        },
        GetChunk::Escaping(GetEscaping::ExpectingColonsThenEscaping) => {
          check_token!(TokenTree2::Punct(sc), thing, "Expected ':' (first part of ::).", sc.as_char() == ':', "Expected ':' (first part of ::).");
          progress = GetChunk::Escaping(GetEscaping::ExpectingColonThenEscaping);
        },
        GetChunk::Escaping(GetEscaping::ExpectingColonThenEscaping) => {
          check_token!(TokenTree2::Punct(sc), thing, "Expected ':' (second part of ::).", sc.as_char() == ':', "Expected ':' (second part of ::).");
          progress = GetChunk::Escaping(GetEscaping::ExpectingEscaping);
        },
        GetChunk::Escaping(GetEscaping::ExpectingEscaping) => {
          check_token!(TokenTree2::Ident(id), thing, "Expected 'Escaping'.", id.to_string() == "Escaping", "Expected 'Escaping'.");
          progress = GetChunk::Escaping(GetEscaping::ExpectingColonsThenEnd);
        },
        GetChunk::Escaping(GetEscaping::ExpectingColonsThenEnd) => {
          check_token!(TokenTree2::Punct(sc), thing, "Expected ':' (first part of ::).", sc.as_char() == ':', "Expected ':' (first part of ::).");
          progress = GetChunk::Escaping(GetEscaping::ExpectingColonThenEnd);
        },
        GetChunk::Escaping(GetEscaping::ExpectingColonThenEnd) => {
          check_token!(TokenTree2::Punct(sc), thing, "Expected ':' (second part of ::).", sc.as_char() == ':', "Expected ':' (second part of ::).");
          progress = GetChunk::Escaping(GetEscaping::ExpectingEnd);
        },
        GetChunk::Escaping(GetEscaping::ExpectingEnd) => {
          cc.escaping_style = match thing.to_string().as_str() {
            "None" => {
              Some(Escaping::None)
            },
            "Double"  => {
              Some(Escaping::Double)
            },
            "Backslash" => {
              Some(Escaping::Backslash)
            },
            _ => {
              return Err("Expecting one, Double, or Backslash.");
            },
          };
          progress = GetChunk::NothingYet;
        },
        GetChunk::Some => {
          // The new TokenStream must be contained inside a TokenTree2:Group
          cc.rest = Some(match thing {
            TokenTree2::Group(group) => {
              let mut inner = group.stream().into_iter();
              check_token!(Some(TokenTree2::Ident(id)),   inner.next(), "Expected 'quote!{...}'.", id.to_string() == "quote", "Expected 'quote!{...}'.");
              check_token!(Some(TokenTree2::Punct(bang)), inner.next(), "Expected '!{...}'.", bang.as_char() == '!', "Expected '!{...}'.");
              match inner.next() {
                Some(TokenTree2::Group(actual)) => Some(actual.stream()),
                _                               => return Err("Expected {...}."),
              }
            },
            _ => {
              return Err("Expected quote!{...}.");
            },
          });
          progress = GetChunk::NothingYet;
        },
      }
    }
    // We actually ignore cc.marker, as we ~ assume that T is correct
    Ok(Configuration {
      allow_prelude: cc.allow_prelude.ok_or("Needed 'allow_prelude'.")?,
      sigil: cc.sigil.ok_or("Needed 'sigil'.")?,
      escaping_style: cc.escaping_style.unwrap_or_default(),
      rest: cc.rest.ok_or("Needed 'rest'.")?,
      _do: PhantomData,
    })
  }
}

#[test]
fn test_configuration_level_passing() {
  let conf1l = Configuration::<DoMarker> {
    allow_prelude: true,
    sigil: Sigil::Tilde,
    escaping_style: Escaping::None,
    rest: None,
    _do: PhantomData,
  };
  let conf2l = Configuration::<DoMarker> {
    allow_prelude: false,
    sigil: Sigil::Dollar,
    escaping_style: Escaping::Double,
    rest: Some(quote!{foo bar baz(1, 2) () "bloop"}),
    _do: PhantomData,
  };
  let conf1ra: Configuration::<DoMarker> = quote!{Configuration::<DoMarker> {
    allow_prelude: true,
    sigil: ~,
    escaping_style: Escaping::None,
    rest: None,
  }}.try_into().unwrap();
  let conf1rb: Configuration::<DoMarker> = quote!{Configuration::<DoMarker> {
    allow_prelude: true,
    sigil: Tilde,
    escaping_style: Escaping::None,
    rest: None,
  }}.try_into().unwrap();
  let tilde = Sigil::Tilde;
  let dollar = Sigil::Dollar;
  let escaping = Escaping::None;
  let conf1rc: Configuration::<DoMarker> = quote!{Configuration::<DoMarker> {
    allow_prelude: true,
    sigil: #tilde,
    escaping_style: #escaping,
    rest: None,
  }}.try_into().unwrap();
  let conf1rd: Configuration::<DoMarker> = quote!{#conf1l}.try_into().unwrap();
  let conf2ra: Configuration::<DoMarker> = quote!{Configuration::<DoMarker> {
    allow_prelude: false,
    sigil: $,
    rest: Some(quote!{foo bar baz(1, 2) () "bloop"}),
  }}.try_into().unwrap();
  let conf2rb: Configuration::<DoMarker> = quote!{Configuration::<DoMarker> {
    allow_prelude: false,
    sigil: Sigil::Dollar,
    rest: Some(quote!{foo bar baz(1, 2) () "bloop"}),
  }}.try_into().unwrap();
  let conf2rc: Configuration::<DoMarker> = quote!{Configuration::<DoMarker> {
    allow_prelude: false,
    sigil: #dollar,
    rest: Some(quote!{foo bar baz(1, 2) () "bloop"}),
  }}.try_into().unwrap();
  let conf2rd: Configuration::<DoMarker> = quote!{#conf2l}.try_into().unwrap();
  assert_eq!(format!("{:?}", conf1l), format!("{:?}", conf1ra));
  assert_eq!(format!("{:?}", conf1l), format!("{:?}", conf1rb));
  assert_eq!(format!("{:?}", conf1l), format!("{:?}", conf1rc));
  assert_eq!(format!("{:?}", conf1l), format!("{:?}", conf1rd));
  assert_eq!(format!("{:?}", conf2l), format!("{:?}", conf2ra));
  assert_eq!(format!("{:?}", conf2l), format!("{:?}", conf2rb));
  assert_eq!(format!("{:?}", conf2l), format!("{:?}", conf2rc));
  assert_eq!(format!("{:?}", conf2l), format!("{:?}", conf2rd));
}

type PeekFn = fn(Cursor) -> bool;

pub trait StartMarker {
  fn name() -> Option<String>;
  //fn type() -> Self::token;
  type token: Parse;// = syn::token::Do;
  fn tokenp() -> PeekFn;// = syn::token::Do;
  type tokend: Parse + ToString + Clone;
  fn token_token() -> TokenStream2;
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
  fn token_token() -> TokenStream2 {
    quote! { do_with_in::DoMarker }
  }
}

#[derive(Debug,Clone)]
pub struct DoMarker;

impl<T: StartMarker + Clone> Default for Configuration<T> {
  fn default() -> Self {
    //dbg!("Configuration<T>::default()");
    Configuration { allow_prelude: true, rest: None, sigil: Default::default(), escaping_style: Default::default(), _do: PhantomData, }
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
          } else if input.peek(Token![~]) {
            input.parse::<Token![~]>()?;
            base_config.sigil = Sigil::Tilde;
          }
        },
        "escaping_style" => {
          input.parse::<Token![:]>()?;
          let es = input.parse::<Ident>().expect("Double, Backslash, or None expected.").to_string();
          match es.as_str() {
            "Double" => {
              base_config.escaping_style = Escaping::Double;
            },
            "Backslash" => {
              base_config.escaping_style = Escaping::Backslash;
            },
            "None" => {
              base_config.escaping_style = Escaping::None;
            },
            x => {
              return Err(err_pos.error(format!("Bad escaping_style within configuration section; found {} when Double, Backslash, or None expected.", x)));
            },
          };
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
pub struct Variables<'a, T: StartMarker + Clone> {
  handlers:    Handlers<'a, T>,
  with_interp: HashMap<String, TokenStream2>,
  no_interp:   HashMap<String, TokenStream2>,
}

impl<'a, T: 'static + StartMarker + Clone> ToTokens for Variables<'a, T> {
  fn to_tokens(&self, tokens: &mut TokenStream2) {
    let t = T::token_token();
    let wi = self.with_interp.iter().map(|(k, v)| quote!{ (#k, quote!{#v}) });
    let ni = self.no_interp.iter().map(|(k, v)| quote!{ (#k, quote!{#v}) });
    let handlers = self.handlers.iter().map(|(k, (v, it))| {
      
      quote!{ (#k, (Box::new(quote!{#it}), quote!{quote!{#it}})) }
    });
    tokens.extend(quote!{
      Variables::<#t> {
        handlers: HashMap::from([#(#handlers),*]),
        with_interp: HashMap::from([#(#wi),*]),
        no_interp: HashMap::from([#(#ni),*]),
      }
    });
  }
}

enum VariableOpts {
  Handlers,
  WithInterp,
  NoInterp,
}

enum VariableChunks {
  NothingYet,
  Name(VariableOpts),
  Equals(VariableOpts),
  HashMap(VariableOpts),
  FirstColon(VariableOpts),
  SecondColon(VariableOpts),
  From(VariableOpts),
}


impl<'a, T> TryFrom<TokenStream2> for Variables<'a, T> where T: StartMarker + Clone {
  type Error = &'static str;
  fn try_from(value: TokenStream2) -> std::result::Result<Self, Self::Error> {
    let mut vars = Variables::<'a, T> { handlers: HashMap::new(), with_interp: HashMap::new(), no_interp: HashMap::new() };
    let mut iter = value.into_iter();
    let inner = unwrap_struct!("Variables", iter, x, ());
    let mut progress = VariableChunks::NothingYet;
    for thing in inner.into_iter() {
      match progress {
        VariableChunks::NothingYet => {
          match thing {
            TokenTree2::Ident(name) => {
              progress = VariableChunks::Name(match name.to_string().as_str() {
                "handlers"     => VariableOpts::Handlers,
                "with_interp"  => VariableOpts::WithInterp,
                "no_interp"    => VariableOpts::NoInterp,
                x              => return Err("Expecting handlers, with_interp, or no_interp."),
              });
            },
            TokenTree2::Punct(comma) if comma.as_char() == ',' => {
              progress = VariableChunks::NothingYet; // We stay at this point in the state machine
            },
            _ => {
              return Err("Expecting handlers, with_interp, or no_interp.");
            },
          }
        },
        VariableChunks::Name(x) => {
          check_token!(TokenTree2::Punct(eq), thing, "Expected ':'", eq.as_char() == ':', "Expected ':'.");
          progress = VariableChunks::Equals(x);
        },
        VariableChunks::Equals(x) => {
          check_token!(TokenTree2::Ident(conf), thing, "Expected 'HashMap'.", conf.to_string() == "HashMap", "Expected 'HashMap'.");
          progress = VariableChunks::FirstColon(x);
        },
        VariableChunks::HashMap(x) => {
          check_token!(TokenTree2::Punct(eq), thing, "Expected ':'", eq.as_char() == ':', "Expected ':'.");
          progress = VariableChunks::FirstColon(x);
        },
        VariableChunks::FirstColon(x) => {
          check_token!(TokenTree2::Punct(eq), thing, "Expected ':'", eq.as_char() == ':', "Expected ':'.");
          progress = VariableChunks::SecondColon(x);
        },
        VariableChunks::SecondColon(x) => {
          check_token!(TokenTree2::Ident(conf), thing, "Expected 'from'.", conf.to_string() == "from", "Expected 'from'.");
          progress = VariableChunks::From(x);
        },
        VariableChunks::From(x) => {
          match thing {
            TokenTree2::Group(from_args) if from_args.delimiter() == proc_macro2::Delimiter::Parenthesis => {
              match from_args.stream().into_iter().next() {
                Some(TokenTree2::Group(array)) if array.delimiter() == proc_macro2::Delimiter::Bracket => {
                  //
                },
                _ => return Err("Expected [...]."),
              }
            },
            _ => return Err("Expected (...)."),
          }
          progress = VariableChunks::NothingYet;
        },
      }
    }
    todo!();
    return Ok(vars);
  }
}

impl<'a, T: 'static + StartMarker + Clone> Default for Variables<'a, T> {
  fn default() -> Self {
    Variables { handlers: genericDefaultHandlers::<'a, T>(), with_interp: HashMap::new(), no_interp: HashMap::new() }
  }
}

pub type Handler<T: StartMarker + Clone> = dyn Fn(Configuration<T>, Variables<T>, Option<TokenStream2>, TokenStream2) -> (Variables<T>, TokenStream2);
pub type Handlers<'a, T: StartMarker + Clone> = HashMap<String, (Box<&'a Handler<T>>, Option<TokenStream2>)>;


pub fn ifHandler<T: StartMarker + Clone>(c: Configuration<T>, v: Variables<T>, data:Option<TokenStream2>, t: TokenStream2) -> (Variables<T>, TokenStream2) {
  (v, quote!{println!("todo");}.into())
}

pub fn concatHandlerInner<T: StartMarker + Clone>(c: Configuration<T>, v: Variables<T>, t: TokenStream2) -> syn::parse::Result<String> {
  let mut accumulator: Vec<String> = Vec::new();
  for token in t.into_iter() {
    if let TokenTree2::Literal(lit) = token.clone() {
      let real_lit = syn::parse_str::<syn::Lit>(&lit.clone().to_string());
      match real_lit {
        Ok(syn::Lit::Str(it)) => accumulator.push(it.value()),
        Ok(x)            => accumulator.push(lit.to_string()),
        Err(err)         => return Err(err),
      }
      //accumulator.push(lit.to_string());
    } else if let TokenTree2::Group(grp) = token.clone() {
      // Recurse into groups
      match concatHandlerInner(c.clone(), v.clone(), grp.stream()) {
        Ok(it)   => accumulator.push(it),
        Err(err) => return Err(err),
      }
    } else {
      let msg = format!("Expected a literal (literal string, number, character or etc), got {}.", token);
      return Err(syn::parse::Error::new_spanned(token, msg));
    }
  }
  let out_str: String = accumulator.into_iter().collect();
  return Ok(out_str);
}

pub fn concatHandler<T: StartMarker + Clone>(c: Configuration<T>, v: Variables<T>, data:Option<TokenStream2>, t: TokenStream2) -> (Variables<T>, TokenStream2) {
  let mut output = TokenStream2::new();
  let mut variables = v.clone();
  let mut stream = t.into_iter();
  let concat_token = stream.next();
  if let Some(TokenTree2::Ident(name)) = concat_token.clone() {
    let mut temp = TokenStream2::new();
    temp.extend(stream);
    let new_token_stream = do_with_in_explicit(temp, c.clone(), v.clone());
    match concatHandlerInner(c.clone(), v.clone(), new_token_stream) {
      Ok(it)   => output.extend(TokenStream2::from(TokenTree2::Literal(proc_macro2::Literal::string(&it)))),
      Err(err) => return (v, err.to_compile_error()),
    }
  } else if let Some(it) = concat_token {
    let msg = format!("Expected 'concat' to absolutely start a concat expression, got {}.", it);
    return (v, quote!{compile_error!{ #msg }}.into());
  }
  return (v, output);
}

pub fn string_to_identHandler<T: StartMarker + Clone>(c: Configuration<T>, v: Variables<T>, data:Option<TokenStream2>, t: TokenStream2) -> (Variables<T>, TokenStream2) {
  let mut output = TokenStream2::new();
  let mut variables = v.clone();
  let mut stream = t.into_iter();
  let string_to_ident_token = stream.next();
  if let Some(TokenTree2::Ident(name)) = string_to_ident_token.clone() {
    let mut temp = TokenStream2::new();
    temp.extend(stream);
    let mut new_token_stream_iter = do_with_in_explicit(temp, c.clone(), v.clone()).into_iter();
    match new_token_stream_iter.next() {
      Some(TokenTree2::Literal(lit)) => {
        let real_lit = syn::parse_str::<syn::Lit>(&lit.clone().to_string());
        match real_lit {
          Ok(syn::Lit::Str(it)) => output.extend(TokenStream2::from(TokenTree2::Ident(proc_macro2::Ident::new(&it.value(), lit.span())))),
          Ok(x)            => return (v, quote!{compile_error!{ "Expected a string." }}.into()),
          Err(err)         => return (v, err.to_compile_error()),
        }
      },
      Some(x) => {
        let msg = format!("Expected a literal, got {}.", x);
        return (v, quote!{compile_error!{ #msg }}.into());
      },
      None    => return (v, quote!{compile_error!{ "No string given; cannot create identifier." }}.into()),
    }
  } else if let Some(it) = string_to_ident_token {
    let msg = format!("Expected 'string_to_ident' to absolutely start a string_to_ident expression, got {}.", it);
    return (v, quote!{compile_error!{ #msg }}.into());
  }
  return (v, output);
}

pub fn forHandler<T: StartMarker + Clone>(c: Configuration<T>, v: Variables<T>, data:Option<TokenStream2>, t: TokenStream2) -> (Variables<T>, TokenStream2) {
  let mut output = TokenStream2::new();
  let mut variables = v.clone();
  let mut stream = t.into_iter();
  let for_token = stream.next();
  if let Some(TokenTree2::Ident(name)) = for_token.clone() {
    match stream.next() {
      Some(TokenTree2::Ident(var_token)) => {
        //variables.with_interp.insert(var_token.to_string(), 
      },
      Some(x) =>{},
      _ =>{},
    }
  } else if let Some(it) = for_token {
    let msg = format!("Expected 'for' to absolutely start a for expression, got {}.", it);
    return (v, quote!{compile_error!{ #msg }}.into());
  } else {
    return (v, quote!{compile_error!{ "For expression stream was unexpectedly empty." }}.into());
  }
  (v, output)
}

enum Operator {
  Plus,
  Times,
  Minus,
  Division,
}

fn arithmeticInternal<T: StartMarker + Clone, N: std::str::FromStr + std::ops::Add<Output=N> + std::ops::Div<Output=N> + std::ops::Mul<Output=N> + std::ops::Sub<Output=N> + std::cmp::PartialOrd + std::cmp::PartialEq>(c: Configuration<T>, v: Variables<T>, t: TokenStream2) -> syn::parse::Result<N> where <N as std::str::FromStr>::Err: std::fmt::Display {
  let mut left: Option<N> = None;
  let mut operator: Option<Operator> = None;
  for token in t.clone().into_iter() {
    match left {
      None => {
        left = match token.clone() {
          TokenTree2::Literal(lit) => Some(syn::parse_str::<syn::LitInt>(&lit.to_string())?.base10_parse::<N>()?),
          TokenTree2::Group(grp) => Some(arithmeticInternal::<T, N>(c.clone(), v.clone(), grp.stream())?),
          it => {
            let msg = format!("Expected number, got {}", it);
            return Err(syn::parse::Error::new_spanned(token, msg));
          },
        }
      },
      Some(num) => {
        match operator {
          None => {
            match token.clone() {
              TokenTree2::Punct(punct) => {
                match punct.as_char() {
                  '+' if punct.spacing() == proc_macro2::Spacing::Alone => {
                    operator = Some(Operator::Plus);
                  },
                  '-' if punct.spacing() == proc_macro2::Spacing::Alone => {
                    operator = Some(Operator::Minus);
                  },
                  '*' if punct.spacing() == proc_macro2::Spacing::Alone => {
                    operator = Some(Operator::Times);
                  },
                  '/' if punct.spacing() == proc_macro2::Spacing::Alone => {
                    operator = Some(Operator::Division);
                  },
                  it   => {
                    let msg = format!("Expected operator such as +, *, -, or /, got {}", it);
                    return Err(syn::parse::Error::new_spanned(token, msg));
                  },
                }
                left = Some(num);
              },
              it => {
                let msg = format!("Expected operator such as +, *, -, or /, got {}", it);
                return Err(syn::parse::Error::new_spanned(token, msg));
              },
            }
          },
          Some(op) => {
            let right = match token.clone() {
              TokenTree2::Literal(lit) => syn::parse_str::<syn::LitInt>(&lit.to_string())?.base10_parse::<N>()?,
              TokenTree2::Group(grp) => arithmeticInternal::<T, N>(c.clone(), v.clone(), grp.stream())?,
              it => {
                let msg = format!("Expected number, got {}", it);
                return Err(syn::parse::Error::new_spanned(token, msg));
              },
            };
            left = Some(match op {
              Operator::Plus     => num + right,
              Operator::Times    => num * right,
              Operator::Minus    => num - right,
              Operator::Division => num / right,
            }); //replace with: left = Some(result) 
            operator = None;
          },
        }
      },
    }
  }
  return match left {
    Some(n) => Ok(n),
    None    => Err(syn::parse::Error::new_spanned(t, "No numbers found.")),
  };
}

pub fn arithmeticHandler<T: StartMarker + Clone>(c: Configuration<T>, v: Variables<T>, data:Option<TokenStream2>, t: TokenStream2) -> (Variables<T>, TokenStream2) {
  let mut output = TokenStream2::new();
  let mut variables = v.clone();
  let mut stream = t.into_iter();
  let ar_token = stream.next();
  if let Some(TokenTree2::Ident(name)) = ar_token.clone() {
    let mut temp = TokenStream2::new();
    temp.extend(stream);
    let new_token_stream = do_with_in_explicit(temp, c.clone(), v.clone());
    let mut new_token_stream_iter = new_token_stream.into_iter();
    match new_token_stream_iter.next() {
      Some(TokenTree2::Ident(var_token)) => {
        let mut temp2 = TokenStream2::new();
        temp2.extend(new_token_stream_iter);
       //variables.with_interp.insert(var_token.to_string(), 
        match var_token.to_string().as_str() {
          a @ ("u64" | "u64u") => {
            let thing = if a == "u64" { proc_macro2::Literal::u64_suffixed } else { proc_macro2::Literal::u64_unsuffixed };
            let out = thing(match arithmeticInternal::<T, u64>(c.clone(), v.clone(), temp2) {
              Ok(x) => x,
              Err(err) => return (v, err.to_compile_error()),
            });
            output.extend(TokenStream2::from(TokenTree2::Literal(out)).into_iter());
          },
          a @ ("u32" | "u32u") => {
            let thing = if a == "u32" { proc_macro2::Literal::u32_suffixed } else { proc_macro2::Literal::u32_unsuffixed };
            let out = thing(match arithmeticInternal::<T, u32>(c.clone(), v.clone(), temp2) {
              Ok(x) => x,
              Err(err) => return (v, err.to_compile_error()),
            });
            output.extend(TokenStream2::from(TokenTree2::Literal(out)).into_iter());
          },
          a @ ("u16" | "u16u") => {
            let thing = if a == "u16" { proc_macro2::Literal::u16_suffixed } else { proc_macro2::Literal::u16_unsuffixed };
            let out = thing(match arithmeticInternal::<T, u16>(c.clone(), v.clone(), temp2) {
              Ok(x) => x,
              Err(err) => return (v, err.to_compile_error()),
            });
            output.extend(TokenStream2::from(TokenTree2::Literal(out)).into_iter());
          },
          a @ ("u8" | "u8u") => {
            let thing = if a == "u8" { proc_macro2::Literal::u8_suffixed } else { proc_macro2::Literal::u8_unsuffixed };
            let out = thing(match arithmeticInternal::<T, u8>(c.clone(), v.clone(), temp2) {
              Ok(x) => x,
              Err(err) => return (v, err.to_compile_error()),
            });
            output.extend(TokenStream2::from(TokenTree2::Literal(out)).into_iter());
          },
          a @ ("i64" | "i64u") => {
            let thing = if a == "i64" { proc_macro2::Literal::i64_suffixed } else { proc_macro2::Literal::i64_unsuffixed };
            let out = thing(match arithmeticInternal::<T, i64>(c.clone(), v.clone(), temp2) {
              Ok(x) => x,
              Err(err) => return (v, err.to_compile_error()),
            });
            output.extend(TokenStream2::from(TokenTree2::Literal(out)).into_iter());
          },
          a @ ("i32" | "i32u") => {
            let thing = if a == "i32" { proc_macro2::Literal::i32_suffixed } else { proc_macro2::Literal::i32_unsuffixed };
            let out = thing(match arithmeticInternal::<T, i32>(c.clone(), v.clone(), temp2) {
              Ok(x) => x,
              Err(err) => return (v, err.to_compile_error()),
            });
            output.extend(TokenStream2::from(TokenTree2::Literal(out)).into_iter());
          },
          a @ ("i16" | "i16u") => {
            let thing = if a == "i16" { proc_macro2::Literal::i16_suffixed } else { proc_macro2::Literal::i16_unsuffixed };
            let out = thing(match arithmeticInternal::<T, i16>(c.clone(), v.clone(), temp2) {
              Ok(x) => x,
              Err(err) => return (v, err.to_compile_error()),
            });
            output.extend(TokenStream2::from(TokenTree2::Literal(out)).into_iter());
          },
          a @ ("i8" | "i8u") => {
            let thing = if a == "i8" { proc_macro2::Literal::i8_suffixed } else { proc_macro2::Literal::i8_unsuffixed };
            let out = thing(match arithmeticInternal::<T, i8>(c.clone(), v.clone(), temp2) {
              Ok(x) => x,
              Err(err) => return (v, err.to_compile_error()),
            });
            output.extend(TokenStream2::from(TokenTree2::Literal(out)).into_iter());
          },
          a @ ("f64" | "f64u") => {
            let thing = if a == "f64" { proc_macro2::Literal::f64_suffixed } else { proc_macro2::Literal::f64_unsuffixed };
            let out = thing(match arithmeticInternal::<T, f64>(c.clone(), v.clone(), temp2) {
              Ok(x) => x,
              Err(err) => return (v, err.to_compile_error()),
            });
            output.extend(TokenStream2::from(TokenTree2::Literal(out)).into_iter());
          },
          a @ ("f32" | "f32u") => {
            let thing = if a == "f32" { proc_macro2::Literal::f32_suffixed } else { proc_macro2::Literal::f32_unsuffixed };
            let out = thing(match arithmeticInternal::<T, f32>(c.clone(), v.clone(), temp2) {
              Ok(x) => x,
              Err(err) => return (v, err.to_compile_error()),
            });
            output.extend(TokenStream2::from(TokenTree2::Literal(out)).into_iter());
          },
          it => {
            let msg = format!("Expected number type (u64, i64, f64, etc), got {}.", it);
            return (v, quote!{compile_error!{ #msg }}.into());
          }
        }
      },
      Some(x) => {},
      _ => {},
    }
  } else if let Some(it) = ar_token {
    let msg = format!("Expected 'arithmetic' first, got {}.", it);
    return (v, quote!{compile_error!{ #msg }}.into());
  } else {
    return (v, quote!{compile_error!{ "Arithmetic expression stream was unexpectedly empty." }}.into());
  }
  (v, output)
}

pub fn actually_escape<T: StartMarker + Clone>(c: Configuration<T>, v: Variables<T>, data:Option<TokenStream2>, t: TokenStream2) -> (Variables<T>, TokenStream2) {
  todo!()
}
pub fn escape<T: StartMarker + Clone>(c: Configuration<T>, v: Variables<T>, data:Option<TokenStream2>, t: TokenStream2) -> (Variables<T>, TokenStream2) {
  match c.escaping_style {
    Escaping::None      => (v, t),
    Escaping::Double    => actually_escape(c, v, data, quote!{ Double #t }),
    Escaping::Backslash => actually_escape(c, v, data, quote!{ Backslash #t }),
  }
}

pub fn actually_unescape<T: StartMarker + Clone>(c: Configuration<T>, v: Variables<T>, data:Option<TokenStream2>, t: TokenStream2) -> (Variables<T>, TokenStream2) {
  todo!()
}
pub fn unescape<T: StartMarker + Clone>(c: Configuration<T>, v: Variables<T>, data:Option<TokenStream2>, t: TokenStream2) -> (Variables<T>, TokenStream2) {
  match c.escaping_style {
    Escaping::None      => (v, t),
    Escaping::Double    => actually_unescape(c, v, data, quote!{ Double #t }),
    Escaping::Backslash => actually_unescape(c, v, data, quote!{ Backslash #t }),
  }
}
 
pub fn run<T: StartMarker + Clone>(c: Configuration<T>, v: Variables<T>, data:Option<TokenStream2>, t: TokenStream2) -> (Variables<T>, TokenStream2) {
  let mut temp = t.into_iter();
  temp.next();
  let mut code = TokenStream2::new();
  code.extend(temp);
  let in_it = do_with_in_explicit(code, c.clone(), v.clone());
  let out = do_with_in_explicit(in_it, c.clone(), v.clone());
  (v, out)
}
// TODO: Remeber to check for whether 'quote' ends up stacking up due to everything inside the $(...) being passed through the t
pub fn quote<T: StartMarker + Clone>(c: Configuration<T>, v: Variables<T>, data:Option<TokenStream2>, t: TokenStream2) -> (Variables<T>, TokenStream2) {
  // Remember that the first token of t should already be 'quote'
  let out = match c.sigil {
    Sigil::Dollar  => quote!{ $(#t) },
    Sigil::Percent => quote!{ %(#t) },
    Sigil::Hash    => quote!{ #(#t) },
    Sigil::Tilde   => quote!{ ~(#t) },
  };
  (v, out)
}

pub fn unquote<T: StartMarker + Clone>(c: Configuration<T>, v: Variables<T>, data:Option<TokenStream2>, t: TokenStream2) -> (Variables<T>, TokenStream2) {
  let mut out: TokenStream2 = quote!{compile_error!{"Nothing here."}}.into();
  let sig_char = format!("{}", c.sigil).pop().expect("Expected Sigil to have a character.");
  let mut stream = t.into_iter();
  check_token_ret!(v, Some(TokenTree2::Ident(uq)), stream.next(), "Expected 'unquote' to be the name of the handler called.", uq.to_string() == "unquote", "Expected 'unquote' to be the name of the handler called.");
  let mut temp = TokenStream2::new();
  temp.extend(stream);
  let mut as_run = do_with_in_explicit(temp, c.clone(), v.clone());
  let mut stream = as_run.into_iter();
  check_token_ret!(v, Some(TokenTree2::Punct(sig)), stream.next(), "Expected a quote.", sig.as_char() == sig_char, "Expected a quote.");
  let tc = stream.next();
  if let Some(TokenTree2::Group(the_call)) = tc.clone() {
    let mut inner_stream = the_call.stream().into_iter();
    check_token_ret!(v, Some(TokenTree2::Ident(q)), inner_stream.next(), "Expected 'quote'.", q.to_string() == "quote", "Expected 'quote'.");
    out = TokenStream2::new();
    out.extend(inner_stream);
  } else {
    let msg = format!("Expected a call body, got {:?}.", tc);
    out = quote!{compile_error!{ #msg }}.into();
  }
  /*
  if let Some(TokenTree2::Punct(p)) = tok.clone() {
    let p_c = p.as_char();
    if p_c == sig_char {
    } else {
      let msg = format!("Expected {}, got {}, inside unquote.", sig_char, p_c);
      out = quote!{compile_error!{ #msg }}.into();
    }
  } else {
    let msg = format!("Expected {}, got {:?}, inside unquote.", sig_char, tok);
    out = quote!{compile_error!{ #msg }}.into();
  }*/
  (v, out)
}

#[derive(Debug,Clone)]
enum LogicBoolOp {
  And,
  Or,
  Not,
  Equals,
  NotEquals,
}
fn logicInternalBool<T: StartMarker + Clone>(c: Configuration<T>, v: Variables<T>, data:Option<TokenStream2>, t: TokenStream2) -> (Variables<T>, TokenStream2) {
  let mut left: Option<bool> = None;
  let mut operator: Option<LogicBoolOp> = None;
  for token in t.clone().into_iter() {
    match left {
      None => {
        left = Some(match token.clone() {
          TokenTree2::Ident(x) if x.to_string() == "true" =>  true,
          TokenTree2::Ident(x) if x.to_string() == "false" => false,
          x => {
            let msg = format!{"Expected true or false on the lhs of a logic expression; got {:?}.", x};
            return (v, quote!{compile_error!{ #msg }});
          },
        });
      },
      Some(inner_left) => {
        match operator {
          None => {
            match token.clone() {
              TokenTree2::Punct(x) if x.as_char() == '&' => {
                operator = Some(LogicBoolOp::And);
              },
              TokenTree2::Punct(x) if x.as_char() == '|' => {
                operator = Some(LogicBoolOp::Or);
              },
              TokenTree2::Punct(x) if x.as_char() == '=' => {
                operator = Some(LogicBoolOp::Equals);
              },
              TokenTree2::Punct(x) if x.as_char() == '^' => {
                operator = Some(LogicBoolOp::NotEquals);
              },
              x => {
                let msg = format!{"Expected & | = or ^ in a logic expression; got {:?}.", x};
                return (v, quote!{compile_error!{ #msg }});
              },
            }
          },
          Some(op) => {
            // token is now the rhs
            let right = match token {
              TokenTree2::Ident(x) if x.to_string() == "true"  => true,
              TokenTree2::Ident(x) if x.to_string() == "false" => false,
              TokenTree2::Group(inner) => {
                let mut rhs = TokenStream2::new();
                rhs.extend(inner.stream());
                let (_, it) = logicInternal(c.clone(), v.clone(), data.clone(), rhs);
                let out = match it.into_iter().next() {
                  Some(TokenTree2::Ident(x)) if x.to_string() == "true"  => true,
                  Some(TokenTree2::Ident(x)) if x.to_string() == "false" => false,
                  x => {
                    let msg = format!{"Expected true or false on the rhs of a logic expression; got {:?}.", x};
                    return (v, quote!{compile_error!{ #msg }});
                  },
                };
                out
              },
              x => {
                let msg = format!{"Expected true or false on the rhs of a logic expression; got {:?}.", x};
                return (v, quote!{compile_error!{ #msg }});
              },
            };
            let out = match op {
              LogicBoolOp::And => {
                inner_left & right
              },
              LogicBoolOp::Or => {
                inner_left | right
              },
              LogicBoolOp::Equals => {
                inner_left == right
              },
              LogicBoolOp::NotEquals => {
                inner_left != right
              },
              x => {
                let msg = format!{"Expected & | = or ^ in a logic expression; got {:?}.", x};
                return (v, quote!{compile_error!{ #msg }});
              },
            };
            return (v, quote!{#out});
          },
        }
      },
    }
  };
  let out = match left {
    None => {
      let msg = format!{"Missed a turn somewhere; left = {:?}, operator = {:?}, t = {:?} .", left, operator, t};
      quote!{compile_error!{ #msg }}
    },
    Some(x) => {
      quote!{#x}
    },
  };
  (v, out)
}

enum NumOp {
  Lt,
  Le,
  Gt,
  Ge,
  Equal,
  NotEqual,
}

fn logicInternalNum<T: StartMarker + Clone, N: std::cmp::PartialOrd + std::cmp::PartialEq + std::str::FromStr>(c: Configuration<T>, v: Variables<T>, data:Option<TokenStream2>, t: TokenStream2, _fake: N) -> (Variables<T>, TokenStream2) where <N as std::str::FromStr>::Err: std::fmt::Debug {
  let mut stream = t.into_iter().peekable();
  let left: N = match stream.next() {
    None => {
      todo!();
    },
    Some(TokenTree2::Literal(x)) => {
      let lit = x.to_string();
      let num: N = N::from_str(&lit).expect("Expected number.");
      num
    },
    Some(_) => todo!(),
  };
  let op: NumOp = match stream.next() {
    Some(TokenTree2::Punct(x)) if x.as_char() == '=' => {
      NumOp::Equal
    },
    Some(TokenTree2::Punct(x)) if x.as_char() == '<' => {
      if let Some(TokenTree2::Punct(eq)) = stream.peek() {
        if eq.as_char() == '=' {
          stream.next();
          NumOp::Le
        } else {
          panic!("Blah!")
        }
      } else {
        NumOp::Lt
      }
    },
    Some(TokenTree2::Punct(x)) if x.as_char() == '>' => {
      if let Some(TokenTree2::Punct(eq)) = stream.peek() {
        if eq.as_char() == '=' {
          stream.next();
          NumOp::Ge
        } else {
          panic!("Blah!")
        }
      } else {
        NumOp::Gt
      }
    },
    Some(TokenTree2::Punct(x)) if x.as_char() == '!' => {
      if let Some(TokenTree2::Punct(eq)) = stream.peek() {
        if eq.as_char() == '=' {
          stream.next();
          NumOp::NotEqual
        } else {
          panic!("Blah!")
        }
      } else {
        panic!("Blah!")
      }
    },
    _ => todo!(),
  };
  let result = match stream.next() {
    Some(TokenTree2::Literal(x)) => {
      let lit = x.to_string();
      let right: N = N::from_str(&lit).expect("Expected number.");
      match op {
        NumOp::Lt       => left <  right,
        NumOp::Le       => left <= right,
        NumOp::Gt       => left >  right,
        NumOp::Ge       => left >= right,
        NumOp::Equal    => left == right,
        NumOp::NotEqual => left != right,
      }
    },
    _ => todo!(),
  };
  (v, quote!{ #result })
}

fn logicInternal<T: StartMarker + Clone>(c: Configuration<T>, v: Variables<T>, data:Option<TokenStream2>, t: TokenStream2) -> (Variables<T>, TokenStream2) {
  let t = do_with_in_explicit(t, c.clone(), v.clone());
  // We check whether it is a number of a bool, and split which one at that point
  let mut to_check = t.clone().into_iter();
  match to_check.next() {
    None => (v, quote!{compile_error!{ "Empty logic expression." }}.into()),
    Some(TokenTree2::Punct(x)) if x.as_char() == '!' => {
      let mut rest = TokenStream2::new();
      rest.extend(to_check);
      let (v, out) = logicInternalBool(c, v, data, rest);
      return match out.into_iter().next() {
        Some(TokenTree2::Ident(x)) if x.to_string() == "true"  => (v, quote!{ false }),
        Some(TokenTree2::Ident(x)) if x.to_string() == "false" => (v, quote!{ true }),
        x => {
          let msg = format!{"Expected a boolean in a not clause, got {:?}", x};
          (v, quote!{compile_error!{ #msg }})
        },
      };
    },
    Some(TokenTree2::Ident(x)) if (x.to_string() == "true") || (x.to_string() == "false") => logicInternalBool(c, v, data, t),
    Some(TokenTree2::Ident(x)) => {
      match x.to_string().as_str() {
        "i8"  => { let mut lin = TokenStream2::new(); lin.extend(to_check); logicInternalNum(c, v, data, lin, 0i8) },
        "u8"  => { let mut lin = TokenStream2::new(); lin.extend(to_check); logicInternalNum(c, v, data, lin, 0u8) },
        "i16" => { let mut lin = TokenStream2::new(); lin.extend(to_check); logicInternalNum(c, v, data, lin, 0i16) },
        "u16" => { let mut lin = TokenStream2::new(); lin.extend(to_check); logicInternalNum(c, v, data, lin, 0u16) },
        "i32" => { let mut lin = TokenStream2::new(); lin.extend(to_check); logicInternalNum(c, v, data, lin, 0i32) },
        "u32" => { let mut lin = TokenStream2::new(); lin.extend(to_check); logicInternalNum(c, v, data, lin, 0u32) },
        "i64" => { let mut lin = TokenStream2::new(); lin.extend(to_check); logicInternalNum(c, v, data, lin, 0i64) },
        "u64" => { let mut lin = TokenStream2::new(); lin.extend(to_check); logicInternalNum(c, v, data, lin, 0u64) },
        "f32" => { let mut lin = TokenStream2::new(); lin.extend(to_check); logicInternalNum(c, v, data, lin, 0.0f32) },
        "f64" => { let mut lin = TokenStream2::new(); lin.extend(to_check); logicInternalNum(c, v, data, lin, 0.0f64) },
        y => {
          let msg = format!("Expected true, false, a literal number, or a numeric type specifier; got {}.", y);
          return (v, quote!{compile_error!{ #msg }}.into());
        }
      }
    }
    Some(TokenTree2::Literal(x)) => logicInternalNum(c, v, data, t, 0i128),
    Some(TokenTree2::Group(x)) => {
      let mut inner = TokenStream2::new();
      inner.extend(x.stream());
      let (_, left) = logicInternal(c.clone(), v.clone(), data.clone(), inner);
      let left_first = left.into_iter().next();
      match left_first {
        None => (v, quote!{compile_error!{ "Empty logic expression." }}.into()),
        Some(TokenTree2::Ident(x)) if (x.to_string() == "true") || (x.to_string() == "false") => {
          let mut new_stream = TokenStream2::new();
          new_stream.extend(TokenStream2::from(TokenTree2::Ident(x)));
          let mut skip_first = t.into_iter();
          skip_first.next();
          new_stream.extend(skip_first);
          logicInternalBool(c, v, data, new_stream)
        },
        Some(TokenTree2::Literal(x)) => {
          let mut new_stream = TokenStream2::new();
          new_stream.extend(TokenStream2::from(TokenTree2::Literal(x)));
          let mut skip_first = t.into_iter();
          skip_first.next();
          new_stream.extend(skip_first);
          logicInternalNum(c, v, data, new_stream, 0i128)
        },
        Some(x) => {
          let msg = format!("Problem in logic lhs; expected true, false, or a number, got {:?}.", x);
          (v, quote!{compile_error!{ #msg }}.into())
        },
      }
    },
    Some(x) => {
      let msg = format!("Problem in logic lhs; expected true, false, or a number, got {:?}.", x);
      (v, quote!{compile_error!{ #msg }}.into())
    }
  }
}

// logic x logic: & | ! ~ = != ~=
// arith x arith: > < = <= >= != ~=
pub fn logicHandler<T: StartMarker + Clone>(c: Configuration<T>, v: Variables<T>, data: Option<TokenStream2>, t: TokenStream2) -> (Variables<T>, TokenStream2) {
  let mut output = TokenStream2::new();
  let mut variables = v.clone();
  let mut stream = t.into_iter();
  let ar_token = stream.next();
  if let Some(TokenTree2::Ident(name)) = ar_token.clone() {
    if name.to_string() == "logic" {
      let mut temp = TokenStream2::new();
      temp.extend(stream);
      let new_token_stream = do_with_in_explicit(temp, c.clone(), v.clone());
      return logicInternal(c, v, data, new_token_stream);
    } else {
      let msg = format!("Expected 'logic' first, got {}.", name);
      return (v, quote!{compile_error!{ #msg }}.into());
    }
  } else if let Some(it) = ar_token {
    let msg = format!("Expected 'logic' first, got {}.", it);
    return (v, quote!{compile_error!{ #msg }}.into());
  } else {
    return (v, quote!{compile_error!{ "Logic expression stream was unexpectedly empty." }}.into());
  }
  (v, output)
}

/*
 * ($fn name(_ foo, _ inner = {default}, bar = {wesf e2f}, named inner_name_2 = {,,, wefi 2we,f 2qwef}) { })
 *
 *
 */
#[derive(Debug,Clone)]
enum FnDefineState {
  LessThanNothing,
  Nothing,
  Name(String),
  NameAnd(String, proc_macro2::Group),
  NameAndAnd(String,  proc_macro2::Group, proc_macro2::Group),
}

#[derive(Debug,Clone)]
enum FnCallState {
  Nothing,
  Name(String),
  NameArgs(String, proc_macro2::Group),
  NameArgsBody(String, proc_macro2::Group, proc_macro2::Group),
}

#[derive(Debug,Clone)]
enum FnArg {
  NoDefault(String),
  Default(String, TokenStream2),
}
#[derive(Debug,Clone)]
struct FnArgs {
  positional: Vec<FnArg>,
  named: HashMap<String, FnArg>,
}
pub fn internalFnRunner<T: StartMarker + Clone>(c: Configuration<T>, v: Variables<T>, data: Option<TokenStream2>, t: TokenStream2) -> (Variables<T>, TokenStream2) {
  let mut stream = t.clone().into_iter();
  let mut state = FnCallState::Nothing;
  match data.clone() {
    None => {
      let msg = format!("Expected a function body, got none, for function call {:?}", t);
      return (v, quote!{compile_error!{ #msg }}.into());
    },
    Some(program) => {
      // First we get the function's name
      if let Some(TokenTree2::Ident(name)) = stream.next() {
        state = FnCallState::Name(name.to_string());
        for token in stream {
          match state {
            FnCallState::Nothing => {
              return (v, quote!{compile_error!{ "Confused state in internalFnRunner." }}.into())
            },
            FnCallState::Name(name) => {
              if let TokenTree2::Group(args) = token.clone() {
                state = FnCallState::NameArgs(name, args);
              } else {
                let msg = format!("Expected a function argument list in the function {} runner data; got {:?}", name, token);
                return (v, quote!{compile_error!{ #msg }}.into());
              }
            },
            FnCallState::NameArgs(name, args) => {
              if let TokenTree2::Group(body) = token.clone() {
                state = FnCallState::NameArgsBody(name, args, body);
              } else {
                let msg = format!("Expected a function body in the function {} runner data; got {:?}", name, token);
                return (v, quote!{compile_error!{ #msg }}.into());
              }
            },
            unexpected => {
              let msg = format!("Got more stuff in the function {} runner data; internal state {:?}, data {:?}", name, unexpected, token);
              return (v, quote!{compile_error!{ #msg }}.into());
            },
          }
        }
        if let FnCallState::NameArgsBody(name, args, body) = state {
          // Create an argument matcher
          let required_args: Vec<String> = Vec::new(); // Put the inner name of each argument with no default in here; we check at the end that we have them all.
          todo!()
        } else {
          (v, quote!{compile_error!{ "Did not have a body in the internal function runner's data." }}.into())
        }
      } else {
        return (v, quote!{compile_error!{ "Expected a named function." }}.into());
      }
    },
  }
}
pub fn fnHandler<T: 'static + StartMarker + Clone>(c: Configuration<T>, v: Variables<T>, data: Option<TokenStream2>, t: TokenStream2) -> (Variables<T>, TokenStream2) {
  let mut variables = v.clone();
  let mut state: FnDefineState = FnDefineState::LessThanNothing;
  for token in t.into_iter() {
    match state.clone() {
      FnDefineState::LessThanNothing => {
        // Consume the initial 'let'
        if let TokenTree2::Ident(name) = token.clone() {
          if name.to_string() == "let" {
            state = FnDefineState::Nothing;
          } else {
            let msg = format!("Expected 'fn' to absolutely start a fn expression, got {}.", token);
            return (v, quote!{compile_error!{ #msg }}.into());
          }
        } else {
          let msg = format!("Expected 'fn' to absolutely start a let expression, got {}.", token);
          return (v, quote!{compile_error!{ #msg }}.into());
        }
      },
      FnDefineState::Nothing => {
        if let TokenTree2::Ident(name) = token {
          state = FnDefineState::Name(name.to_string());
        } else {
          let msg = format!("Expected a function name to start a fn expression, got {}.", token);
          return (v, quote!{compile_error!{ #msg }}.into());
        }
      },
      FnDefineState::Name(name) => {
        if let TokenTree2::Group(args) = token {
          state = FnDefineState::NameAnd(name, args);
        } else {
          let msg = format!("Expected an arglist, got {}.", token);
          return (v, quote!{compile_error!{ #msg }}.into());
        }
      },
      FnDefineState::NameAnd(name, args) => {
        if let TokenTree2::Group(body) = token {
          state = FnDefineState::NameAndAnd(name, args, body);
        } else {
          let msg = format!("Expected a function body, got {}.", token);
          return (v, quote!{compile_error!{ #msg }}.into());
        }
      },
      FnDefineState::NameAndAnd(name, args, body) => {
        let mut stream = TokenStream2::new();
        stream.extend(TokenStream2::from(TokenTree2::Group(args)).into_iter());
        stream.extend(TokenStream2::from(TokenTree2::Group(body)).into_iter());
        variables.handlers.insert(name, (Box::new(&internalFnRunner), Some(stream)));
      },
    }
  }
  
  (variables, quote!{ } )
}

#[derive(Debug,Clone,PartialEq,Eq)]
enum LetState {
  LessThanNothing,
  Nothing,
  Name(String),
  NamePostEquals(String),
}
pub fn letHandler<T: StartMarker + Clone>(c: Configuration<T>, v: Variables<T>, data: Option<TokenStream2>, t: TokenStream2) -> (Variables<T>, TokenStream2) {
  let mut variables = v.clone();
  let mut state: LetState = LetState::LessThanNothing;

  for token in t.into_iter() {
    match state.clone() {
      LetState::LessThanNothing => {
        // Consume the initial 'let'
        if let TokenTree2::Ident(name) = token.clone() {
          if name.to_string() == "let" {
            state = LetState::Nothing;
          } else {
            let msg = format!("Expected 'let' to absolutely start a let expression, got {}.", token);
            return (v, quote!{compile_error!{ #msg }}.into());
          }
        } else {
          let msg = format!("Expected 'let' to absolutely start a let expression, got {}.", token);
          return (v, quote!{compile_error!{ #msg }}.into());
        }
      },
      LetState::Nothing => {
        if let TokenTree2::Ident(name) = token {
          state = LetState::Name(name.to_string());
        } else {
          let msg = format!("Expected a variable name to start a let expression, got {}.", token);
          return (v, quote!{compile_error!{ #msg }}.into());
        }
      },
      LetState::Name(var_name) => {
        if let TokenTree2::Punct(punct) = token.clone() {
          if punct.as_char() == '=' && punct.spacing() == proc_macro2::Spacing::Alone {
            state = LetState::NamePostEquals(var_name);
          } else {
            let msg = format!("Expected '=', got {}.", token);
            return (v, quote!{compile_error!{ #msg }}.into());
          }
        } else {
          let msg = format!("Expected '=', got {}.", token);
          return (v, quote!{compile_error!{ #msg }}.into());
        }
      },
      LetState::NamePostEquals(var_name) => {
        if let TokenTree2::Group(body) = token {
          variables.no_interp.insert(var_name, body.stream());
          state = LetState::Nothing;
        } else {
          let msg = format!("Expected a curly bracket surrounded expression (the value to put in the variable), got {}.", token);
          return (v, quote!{compile_error!{ #msg }}.into());
       }
      },
    }
  }
  (variables, quote!{}.into())
}

pub fn varHandler<T: StartMarker + Clone>(c: Configuration<T>, v: Variables<T>, data:Option<TokenStream2>, t: TokenStream2) -> (Variables<T>, TokenStream2) {
  let mut variables = v.clone();
  let mut state: LetState = LetState::LessThanNothing;

  for token in t.into_iter() {
    match state.clone() {
      LetState::LessThanNothing => {
        // Consume the initial 'let'
        if let TokenTree2::Ident(name) = token.clone() {
          if name.to_string() == "var" {
            state = LetState::Nothing;
          } else {
            let msg = format!("Expected 'var' to absolutely start a let expression, got {}.", token);
            return (v, quote!{compile_error!{ #msg }}.into());
          }
        } else {
          let msg = format!("Expected 'var' to absolutely start a let expression, got {}.", token);
          return (v, quote!{compile_error!{ #msg }}.into());
        }
      },
      LetState::Nothing => {
        if let TokenTree2::Ident(name) = token {
          state = LetState::Name(name.to_string());
        } else {
          let msg = format!("Expected a variable name to start a var expression, got {}.", token);
          return (v, quote!{compile_error!{ #msg }}.into());
        }
      },
      LetState::Name(var_name) => {
        if let TokenTree2::Punct(punct) = token.clone() {
          if punct.as_char() == '=' && punct.spacing() == proc_macro2::Spacing::Alone {
            state = LetState::NamePostEquals(var_name);
          } else {
            let msg = format!("Expected '=', got {}.", token);
            return (v, quote!{compile_error!{ #msg }}.into());
          }
        } else {
          let msg = format!("Expected '=', got {}.", token);
          return (v, quote!{compile_error!{ #msg }}.into());
        }
      },
      LetState::NamePostEquals(var_name) => {
        if let TokenTree2::Group(body) = token {
          let to_insert = do_with_in_explicit(body.stream(), c.clone(), variables.clone());
          variables.with_interp.insert(var_name, to_insert);
          state = LetState::Nothing;
        } else {
          let msg = format!("Expected a curly bracket surrounded expression (the value to put in the variable), got {}.", token);
          return (v, quote!{compile_error!{ #msg }}.into());
       }
      },
    }
  }
  (variables, quote!{}.into())
}

pub fn genericDefaultHandlers<'a, T: 'static + StartMarker + Clone>() -> Handlers<'a, T> {
  let mut m: HashMap<String, (Box<&Handler<T>>, Option<TokenStream2>)> = HashMap::new();
  m.insert(String::from("if"), ((Box::new(&ifHandler), None)));
  m.insert(String::from("let"), ((Box::new(&letHandler), None)));
  m.insert(String::from("var"), ((Box::new(&varHandler), None)));
  m.insert(String::from("concat"), ((Box::new(&concatHandler), None)));
  m.insert(String::from("string_to_ident"), ((Box::new(&string_to_identHandler), None)));
  m.insert(String::from("arithmetic"), ((Box::new(&arithmeticHandler), None)));
  m.insert(String::from("logic"), ((Box::new(&logicHandler), None)));
  m.insert(String::from("fn"), ((Box::new(&fnHandler), None)));
  m.insert(String::from("quote"), ((Box::new(&quote), None)));
  m.insert(String::from("unquote"), ((Box::new(&unquote), None)));
  m.insert(String::from("escape"), ((Box::new(&escape), None)));
  m.insert(String::from("unescape"), ((Box::new(&unescape), None)));
  m.insert(String::from("run"), ((Box::new(&run), None)));
  m
}

pub fn do_with_in_internal(t: TokenStream2) -> TokenStream2 {
  // Check for configuration first
  match syn::parse2::<Configuration<DoMarker>>(t) {
    Ok(it) => {
      let mut configuration = it.clone();
      
      let out = match configuration.clone().rest {
        Some(out) => out,
        None      => TokenStream2::new().into(),
      };
      // For now to make testing possible
      configuration.rest = None;
      do_with_in_explicit(TokenStream2::from(out), configuration, Variables::default()).into()
    },
    Err(it) =>  it.to_compile_error().into()  // we actually want to early exit here, not do: do_with_in_explicit(it.to_compile_error().into(), Configuration::<DoMarker>::default(), defaultHandlers()),
  }
}


pub fn do_with_in_explicit<'a, T: StartMarker + Clone>(t: TokenStream2, c: Configuration<T>, v: Variables<'a, T>) -> TokenStream2 {
  let mut output = TokenStream2::new();
  let mut use_vars = v;
  //check for variables to insert
  //check for handlers to run
  //insert token
  let token_char = match c.clone().sigil {
    Sigil::Dollar  => '$',
    Sigil::Percent => '%',
    Sigil::Hash    => '#',
    Sigil::Tilde   => '~',
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
              if let Some((handler, data)) = use_vars.clone().handlers.get(&first.to_string()) {
                let (new_vars, more_output) = handler(c.clone(), use_vars.clone(), data.clone(), stream);
                use_vars = new_vars;
                output.extend(more_output);
              }
            }

            //if let Some(handler) = v.handlers.get(
          }
        } else {
          let delim = group.clone().delimiter();
          output.extend(TokenStream2::from(TokenTree2::Group(
                proc_macro2::Group::new(delim, do_with_in_explicit(group.stream(), c.clone(), use_vars.clone()))
          )));
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

#[test]
fn conf_test_panic1() {
  let input: TokenStream2 = quote! {sigil: % ow2eihf do wiwlkef }.into();
  let output = do_with_in_internal(input);
  assert_eq!(format!("{}", output), format!("{}", TokenStream2::from(quote! {compile_error!{ "Bad configuration section; found ow2eihf when sigil or end of prelude expected" }} )));
}


