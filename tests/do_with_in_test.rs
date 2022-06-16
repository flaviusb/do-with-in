#[macro_use]
extern crate do_with_in;

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


