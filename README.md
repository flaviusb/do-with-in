# do-with-in

This is a set of Rust packages that provides a basic form of use-site metaprogramming via staging for proc\_macros.

## What?

In its simplest form, you can wrap the invocation of some other proc\_macro with `do_with_in!` in order to do metaprogramming during the invocation of the thing - that is, in the input itself - using a fairly basic language. We don't have true unquote-splicing, as that is more or less impossible in Rust.

But ultimately, this package was made to allow for a specific kind of refactoring in my [fantasy cpu emulator](https://github.com/flaviusb/fantasy-cpu-emulator) that I could not achieve otherwise. Hopefully this will prove useful to other people as well.

## Maybe an example?

There is an example of the use of `do_with_in!` for use site metaprogramming here: `examples/typed-html.rs`, and the tests at `do_with_in_internal_macros/tests/do_with_in_test.rs` are the closest I have at the moment to documenting how to use the various functionalities provided.
