#[macro_use]
extern crate do_with_in_internal_macros;

use do_with_in::*;
use typed_html::html;
use typed_html::dom::DOMTree;
fn main() {
  do_with_in!{
    sigil: ~
    do
    ~(let list_type = {ul})
    ~(mk list <~list_type> ~(run ~1) </~list_type>)
    ~(mk item <li> ~(run ~1) </li>)
    let mut thing: DOMTree<String> = html!{
      <html>
        <head>
          <title>"Example of use site metaprogramming."</title>
        </head>
        <body>
          ~(list
            {
              ~(item {"First item."})
              ~(item {"Second item."})
              ~(item {"Third item."})})
        </body>
      </html>
    };
  };
  let out = thing.to_string();
  println!("{}", out);
}
