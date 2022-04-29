extern crate proc_macro;
extern crate syn;
#[macro_use] extern crate quote;
extern crate proc_macro2;

use proc_macro::{TokenStream, TokenTree};

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
struct Configuration {
  allow_prelude: bool,
  sigil: Sigil,
}

impl Default for Configuration {
  fn default() -> Self {
    Configuration { allow_prelude: true, ..Default::default() }
  }
}

#[derive(Debug,Copy,Clone,PartialEq,Eq)]
struct Variables {}

type Handler = dyn Fn(Configuration, Variables, TokenStream) -> (Variables, TokenStream);
type Handlers = HashMap<String, Box<Handler>>;


fn ifHandler(c: Configuration, v: Variables, t: TokenStream) -> (Variables, TokenStream) {
  (v, t)
}

fn defaultHandlers() -> Handlers {
  let mut m: HashMap<String, Box<Handler>> = HashMap::new();
  m.insert(String::from("if"), Box::new(ifHandler));
  m
}

/*
fn defaultConfiguration() -> ...

#[proc_macro]
fn do_with_in(t: TokenStream) -> TokenStream {
  // Check for configuration first
  let mut configuration = defaultConfiguration();
  while(t.peek().toString() != "do") {
    match t.next().toString() {
      ... => 
    }
  }
  do_with_in_explicit(t, configuration)
}

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
