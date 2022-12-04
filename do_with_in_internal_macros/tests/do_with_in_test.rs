#[macro_use]
extern crate do_with_in_internal_macros;

#[test]
fn empty_test() {
  do_with_in!();
}

#[test]
fn conf_test() {
  do_with_in!(sigil: $ do);
}

#[test]
fn conf_test2() {
  do_with_in!(sigil: % do println!("test"); );
}

#[test]
fn conf_test3() {
  do_with_in!(do let foo = 3; );
}

#[test]
fn handler_test1() {
  do_with_in!(
    sigil: $
    do 
      $(if foo then bar else baz);
      println!("After an if");
  );
}

#[test]
fn let_nointerp_test1() {
  let mut x = 3;
  do_with_in!(
    sigil: %
    do
    %(let foo = { 5; })
    x = %foo
  );
  assert_eq!(x, 5);
}

#[test]
fn let_nointerp_test2() {
  let mut x = 3;
  do_with_in!(
    sigil: %
    do
    %(let
      foo = { 5; }
      bar = {let y = "bar"; })
    x = %foo;
    %bar
  );
  assert_eq!(x, 5);
  assert_eq!(y, "bar");
}

#[test]
fn let_interp_test1() {
  let mut x = 3;
  do_with_in!(
    sigil: %
    do
    %(let foo = { 5; })
    %(var bar = { %foo })
    x = %bar
  );
  assert_eq!(x, 5);
}

#[test]
fn concat_test1() {
  do_with_in! {
    sigil: $
    do
    let x = $(concat 1 "abc" 2);
  }
  assert_eq!(x, "1abc2");
}

#[test]
fn concat_test2() {
  do_with_in! {
    sigil: $
    do
    let x = $(concat 1 "a\"b\\c" 2);
  }
  assert_eq!(x, "1a\"b\\c2");
}

#[test]
fn string_to_ident_test1() {
  do_with_in!{
    sigil: $
    do
    $(let i = {3})
    $(var x = {$(concat "foo" "_" $i)});
    let $(string_to_ident $x) = $i;
    let $(string_to_ident $(concat $x "_" $x)) = $i * $i;
  }
  assert_eq!(foo_3, 3);
  assert_eq!(foo_3_foo_3, 9);
}

#[test]
fn arithmetic_test1() {
  do_with_in!{
    sigil: $
    do
    let x = $(arithmetic u64 1 + 1 + 1);
    $(var z = {$(arithmetic f64 4 * 6 / (1 + 4))})
    let n = $(concat "The number: " $z);
  }
  assert_eq!(x, 3);
  assert_eq!(n, "The number: 4.8f64");
}

#[test]
fn mumble_test() {
  do_with_in!{
    sigil: ~
    do
    ~(let
     prefix = {"foo"}
     base = {3}
    )
    fn ~(string_to_ident ~(concat ~prefix "_" ~(arithmetic u64u 1 + ~base))) (it: u64) -> u64 {
      it * ~base
    }
  }
  assert_eq!(foo_4(4), 12);
}

#[test]
fn quote_test() {
  do_with_in!{
    sigil: ~
    escaping_style: Double
    do
      ~(let
        thing = {~(quote ~x + ~y)}
        )
      ~(let
        x = {3}
        y = {4}
        )
      let z = ~(run ~(unquote ~thing));
  }
  assert_eq!(z, 7);
}

#[test]
fn quote_more_test() {
  do_with_in!{
    sigil: ~
    escaping_style: Double
    do
      ~(let
        x = {1}
        y = {2}
        )
      ~(var
        thing  = {~(quote ~x + ~y)}
        thing2 = {~(arithmetic u64 ~x + ~y)}
        thing3 = {~x + ~y}
        )
      ~(let
        x = {3}
        y = {4}
        )
      let z1 = ~(run ~(unquote ~thing));
      let z2 = ~thing2;
      let z3 = ~thing3;
  }
  assert_eq!(z1, 7);
  assert_eq!(z2, 3);
  assert_eq!(z3, 3);
}

#[test]
fn basic_logic_test() {
  do_with_in!{
    sigil: #
    do
    let x1 = #(logic false | true);
    let x2 = #(logic false | false);
    let x3 = #(logic (! false) | false);
    let x4 = #(logic true | true);
    let x5 = #(logic true | false);
    let x6 = #(logic false ^ true);
    let x7 = #(logic false ^ false);
    let x8 = #(logic false & true);
    let x9 = #(logic true & true);
    let xa = #(logic false = true);
    let xb = #(logic false = false);
    let xc = #(logic true);
    let xd = #(logic ! true);
    let xe = #(logic true = (false ^ true));
    let xf = #(logic (false | (! false)) | ((true = true) & (! false)));
  }
  assert_eq!(x1, true);
  assert_eq!(x2, false);
  assert_eq!(x3, true);
  assert_eq!(x4, true);
  assert_eq!(x5, true);
  assert_eq!(x6, true);
  assert_eq!(x7, false);
  assert_eq!(x8, false);
  assert_eq!(x9, true);
  assert_eq!(xa, false);
  assert_eq!(xb, true);
  assert_eq!(xc, true);
  assert_eq!(xd, false);
  assert_eq!(xe, true);
  assert_eq!(xf, true);
}

/*#[test]
fn for_test1() {
  do_with_in!{
    sigil: $
    do
    $(var i = {0})
    $(var b = {[(a + b) (a * b) (a)]})
    $(for x in %b {
      fn $(string_to_ident $(concat "function_" $i)) (a: i64, b: i64) -> i64 {
        $x
      }
      $(var i = {$(arithmetic $i + 1)})
    })
  }
  assert_eq!(function_0(1, 2), 3);
  assert_eq!(function_1(1, 2), 2);
  assert_eq!(function_2(1, 2), 1);
}*/


/*
** should panic doesn't actually work when erroring out when running a proc macro
#[test]
#[should_panic(expected = "Bad configuration")]
fn conf_test_panic() {
  do_with_in!(ofhqoeiwhfoqw sigil: % ow2eihf do wiwlkef );
}

#[test]
#[should_panic(expected = "Bad configuration; found ow2eihf at")]
fn conf_test_panic2() {
  do_with_in!(sigil: % ow2eihf do wiwlkef );
}
*/


