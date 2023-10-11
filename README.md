# do-with-in

[![crates.io](https://img.shields.io/crates/v/do-with-in.svg)](https://crates.io/crates/do-with-in)
[![License: GPL-3.0-only](https://img.shields.io/crates/l/do-with-in)](https://spdx.org/licenses/GPL-3.0-only.html)

A template language for Rust metaprogramming using partial staging.

This crate lets you run code at compile time to produce the tokens other proc_macros will consume. It is also useful for ad-hoc in-place code generation, and for making templates (like Jinja or Mustache) for your code. It uses its own simple inner language based on handlers, variables, and a user-chosen sigil. The stage separation model of Rust does impose some limitations on what this crate can do.

## Table of Contents

- [Background](#background)
- [Install](#install)
- [Usage](#usage)
- [API](#api)
- [Built-in Handlers](#built-in-handlers)
- [License](#license)

## Background

Ultimately, this package was made to allow for a specific kind of refactoring in my [fantasy cpu emulator](https://github.com/flaviusb/fantasy-cpu-emulator) that I could not achieve otherwise. Hopefully this will prove useful to other people as well.

### Limitations

We don't have true unquote-splicing, as that is more or less impossible in Rust.

## Install

    cargo add do-with-in

## Usage

In its simplest form, you can wrap the invocation of some other proc\_macro with `do_with_in!` in order to do metaprogramming during the invocation of the thing - that is, in the input itself - using a fairly basic language.

```rust
#[macro_use]
extern crate do_with_in;

use do_with_in::*;
// ...
fn main() {
    do_with_in!{
        sigil: ~ // One of $, %, #, or ~
        do // Separates front matter from body
        // Define a handler called `header` that wraps its argument
        ~(mk header <head><title> ~(run ~1) </title></head>)

        html!{
            <html>
                ~(header {"My title"})
            </html>
        }
    }
// ...
}
```

There is an example of the use of `do_with_in!` for use site metaprogramming here: `examples/typed-html.rs`, and the tests at `do_with_in_internal_macros/tests/do_with_in_test.rs` are the closest I have at the moment to documenting how to use the various functionalities provided.

## API

### `do_with_in!()`

This is the proc\_macro most users of this crate will use.

There is front matter, which can define the sigil. Then `do`, then after that is where the metaprogramming can happen.

In the metaprogramming section, variables are identifiers with a sigil prepended. You can create and assign to them with `let` and `var` handlers. Numbers with a sigil prepended are special variables that can be set inside a handler; you cannot assign to them with let or var. Brackets with a sigil prepended start a handler invocation; the handler invoked will be the first token inside the brackets, which must be an identifier.

## Built-In Handlers

See [`fn.genericDefaultHandlers`][] for the full list of built-in handlers.

[`fn.genericDefaultHandlers`]: https://docs.rs/do-with-in/0.1.1/do_with_in/fn.genericDefaultHandlers.html

### `let` & `var`

Create and assign variables, identifiers with a prepended sigil. The difference between the two is that `let` does not interpolate during either variable definition or use, whereas `var` interpolates both.

The value assigned to avariable defined with `let` will remain unchanged before it is used:

    %(let bar = {let y = "bar"; })
    %bar
    //  y == "bar"

Whereas a variable set with `var` can make reference to other metaprogramming variables:

    %(let foo = { 5; })
    %(var bar = { %foo })
    x = %bar
    // x == 5

### `run`

Evaluate block of code

### `mk` *identifier* *block*

A simple way to define new handlers at the use site. Allows the use of positional numbered parameters e.g. `~1`.

    // mk defines the handler..
    ~(mk embolden <b> ~(run ~1) </b>)
    // .. which can then be called with arguments
    ~(embolden {"World"})

### `concat` *params*

Concatenates its arguments into a string.

    let x = $(concat 1 "abc" 2);
    // x == "1abc2"

### `withSigil` *newSigil* *params*

Redefine which sigil to use for the scope of the handler.

    $(let a = {"foo"})
    let a = $(withSigil # #(concat #a "bar"));

### `import`

Basic file inclusion. Path is specified by quoted segments; special unquoted identier Base is used for the crate root.

    $(import Base "src" "import.$")

A `file:` hint can be included in the front matter to allow import to use a relative path.

    do_with_in!{
      file: "src/importable.rs"
      sigil: $
      do
      $(import "import.$")
    }


## License

[GPL-3.0-only © flaviusb](https://spdx.org/licenses/GPL-3.0-only.html).

SEE LICENSE IN [LICENSE](../LICENSE) file.