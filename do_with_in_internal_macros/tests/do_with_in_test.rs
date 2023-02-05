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
    #(var
      y = {false}
      z = {#(logic #y ^ true)}
    )
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
    let xy = #(logic ! #y);
    let xz = #(logic (#y | (! #z)) & (#y = #z));
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
  assert_eq!(xy, true);
  assert_eq!(xz, false);
}

#[test]
fn basic_logic_arithmetic_test() {
  do_with_in!{
    sigil: #
    do
    let aa = #(logic 3 > 4);
    let ab = #(logic 4 > 4);
    let ac = #(logic 4 > 3);
    let ad = #(logic 3 < 4);
    let ae = #(logic 4 < 4);
    let af = #(logic 4 < 3);
    let ba = #(logic 3 >= 4);
    let bb = #(logic 4 >= 4);
    let bc = #(logic 4 >= 3);
    let bd = #(logic 3 <= 4);
    let be = #(logic 4 <= 4);
    let bf = #(logic 4 <= 3);
    let ca = #(logic 3 = 4);
    let cb = #(logic 4 = 4);
    let cc = #(logic 4 = 3);
    let cd = #(logic 3 != 4);
    let ce = #(logic 4 != 4);
    let cf = #(logic 4 != 3);
  }
  assert_eq!(aa, false);
  assert_eq!(ab, false);
  assert_eq!(ac, true);
  assert_eq!(ad, true);
  assert_eq!(ae, false);
  assert_eq!(af, false);
  assert_eq!(ba, false);
  assert_eq!(bb, true);
  assert_eq!(bc, true);
  assert_eq!(bd, true);
  assert_eq!(be, true);
  assert_eq!(bf, false);
  assert_eq!(ca, false);
  assert_eq!(cb, true);
  assert_eq!(cc, false);
  assert_eq!(cd, true);
  assert_eq!(ce, false);
  assert_eq!(cf, true);
}

#[test]
fn if_test() {
  do_with_in!{
    sigil: $
    do
      $(let
        x = {3}
        y = {4})

      $(if {$(logic $x < $y)} {let a = $y * 5;} {assert_eq!(4, $y);})
      $(if {$(logic $x > $y)} {let b = $y * 5;} {assert_eq!(4, $y);})
      $(if {true}  {assert_eq!(true, true);}  {assert_eq!(true, false);})
      $(if {false} {assert_eq!(true, false);} {assert_eq!(true, true);})
  };
  assert_eq!(a, 20);
}

#[test]
fn array_length_test() {
  do_with_in!{
    sigil: %
    do
    let i = %(array length {{1} {4 5} {pub fun foo() -> u8 { 4 } }});
    let j = %(array length {{1}});
    let k = %(array length {});
    let l = %(array q length %(quote {{1} {4 5} {pub fun foo() -> u8 { 4 } }}));
    let m = %(array q length %(quote {{1}}));
    let n = %(array q length %(quote {}));
    %(let
      item         = {{3 4 5}}
      item2        = {{3 4 5}}
      arr          = { {{1 2 3} {4 5 6} {3} {}} }
      quoted_array = {%(quote {{1 2 3} {4 5 6} {3} {}} )}
    )
    let o = %(array length %arr);
    let p = %(array length { %item {wodi wed wowfn} %item2 });
    let q = %(array q length %quoted_array);
  };
  assert_eq!(i, 3);
  assert_eq!(j, 1);
  assert_eq!(k, 0);
  assert_eq!(l, 3);
  assert_eq!(m, 1);
  assert_eq!(n, 0);
  assert_eq!(o, 4);
  assert_eq!(p, 3);
  assert_eq!(q, 4);
}

#[test]
fn test_array_mk() {
  do_with_in!{
    sigil: $
    do
    let out = $(array length $(array mk {2} {23 1254 4} {& ^ %}));
    let quoted_out = $(array q length $(array q mk $(quote {2}) $(quote {23 1254 4}) $(quote {& ^ %})));
  };
  assert_eq!(out, 3);
  assert_eq!(quoted_out, 3);
}

#[test]
fn test_array_concat() {
  do_with_in!{
    sigil: $
    do
    let out = $(array length $(array concat [{2}] [{23 1254 4} {& ^ %}]));
    let quoted_out = $(array q length $(array q concat $(quote [{2}]) $(quote [{23 1254 4} {& ^ %}])));
    $(let
      out2 = { [{werftg wefg } { wf} {^#@} {"ewgfw" 'f'}] }
      quoted_out2 = {$(quote [{werftg wefg } { wf} {^#@} {"ewgfw" 'f'}] )}
    )
    let out2 = $(array length $(array concat $out2 [{23 1254 4} {& ^ %}]));
    let quoted_out2 = $(array q length $(array q concat $quoted_out2 $(quote [{23 1254 4} {& ^ %}])));
  };
  assert_eq!(out, 3);
  assert_eq!(quoted_out, 3);
  assert_eq!(out2, 6);
  assert_eq!(quoted_out2, 6);
}

#[test]
fn array_ith_get_test() {
  do_with_in!{
    sigil: $
    do
    $(let
      out2 = { [{7} { wf} {^#@} {"ewgfw"}] }
      quoted_out2 = {$(quote [{7} { wf} {^#@} {"ewgfw"}] )}
    )
    let wf = 1;
    let out = $(array ith get head $(array concat $out2 [{23 1254 4} {& ^ %}]));
    let out2 = $(array ith get 0 $(array concat $out2 [{23 1254 4} {& ^ %}]));
    let out3 = $(array ith get 1 $(array concat $out2 [{23 1254 4} {& ^ %}]));
    let out4 = $(array ith get tail $(array concat $out2 [{23 1254 4} {'i'}]));
    let out5 = $(array ith get -3 $(array concat $out2 [{23 1254 4} {& ^ %}]));
    let quoted_out = $(array q ith get head $(array q concat $quoted_out2 $(quote [{23 1254 4} {& ^ %}])));
    let quoted_out2 = $(array q ith get 0 $(array q concat $quoted_out2 $(quote [{23 1254 4} {& ^ %}])));
    let quoted_out3 = $(array q ith get 1 $(array q concat $quoted_out2 $(quote [{23 1254 4} {& ^ %}])));
    let quoted_out4 = $(array q ith get tail $(array q concat $quoted_out2 $(quote [{23 1254 4} {'i'}])));
    let quoted_out5 = $(array q ith get -3 $(array q concat $quoted_out2 $(quote [{23 1254 4} {& ^ %}])));
  };
  assert_eq!(out, 7);
  assert_eq!(out2, 7);
  assert_eq!(out3, 1);
  assert_eq!(out4, 'i');
  assert_eq!(out5, "ewgfw");
  assert_eq!(quoted_out, 7);
  assert_eq!(quoted_out2, 7);
  assert_eq!(quoted_out3, 1);
  assert_eq!(quoted_out4, 'i');
  assert_eq!(quoted_out5, "ewgfw");
}

#[test]
fn array_ith_set_test() {
  do_with_in!{
    sigil: $
    do
    $(var
      out = { $(array ith set head [100] [{23 1254 4} {& ^ %}])}
      out3 = { $(array ith set 1 [100] [{23 1254 4} {& ^ %}])}
      out5 = { $(array ith set -1 [100] [{23 1254 4} {& ^ %}])}
      quoted_out = { $(array q ith set head $(quote [100]) $(quote [{23 1254 4} {& ^ %}]))}
      quoted_out3 = { $(array q ith set 1 $(quote [100]) $(quote [{23 1254 4} {& ^ %}]))}
      quoted_out5 = { $(array q ith set -1 $(quote [100]) $(quote [{23 1254 4} {& ^ %}]))}
    )
    let out = $(naiveStringifier $out);
    let out2 = $(array ith get 0 $(array concat $out [{23 1254 4} {& ^ %}]));
    let out3 = $(array ith get 1 $(array concat $out3 [{23 1254 4} {& ^ %}]));
    let out4 = $(array ith get tail $out5);
    let out5 = $(array ith get tail $(array concat $out5 [{23 1254 4} {'i'}]));
    let out6 = $(array ith get -3 $(array concat $out5 [{23 1254 4} {& ^ %}]));
    let quoted_out = $(naiveStringifier $quoted_out);
    let quoted_out2 = $(array q ith get 0 $(array q concat $quoted_out $(quote [{23 1254 4} {& ^ %}])));
    let quoted_out3 = $(array q ith get 1 $(array q concat $quoted_out3 $(quote [{23 1254 4} {& ^ %}])));
    let quoted_out4 = $(array q ith get tail $quoted_out5);
    let quoted_out5 = $(array q ith get tail $(array q concat $quoted_out5 $(quote [{23 1254 4} {'i'}])));
    let quoted_out6 = $(array q ith get -3 $(array q concat $quoted_out5 $(quote [{23 1254 4} {& ^ %}])));
  };
  assert_eq!(out, "[{ 100 } { & ^ % }]"); // This test may be flaky in future; naive stringification might change without warning
  assert_eq!(out2, 100);
  assert_eq!(out3, 100);
  assert_eq!(out4, 100);
  assert_eq!(out5, 'i');
  assert_eq!(out6, 100);
  assert_eq!(quoted_out, "$(quote [{ 100 } { & ^ % }])"); // This test may be flaky in future; naive stringification might change without warning
  assert_eq!(quoted_out2, 100);
  assert_eq!(quoted_out3, 100);
  assert_eq!(quoted_out4, 100);
  assert_eq!(quoted_out5, 'i');
  assert_eq!(quoted_out6, 100);
}

#[test]
fn array_ith_remove_test() {
  do_with_in!{
    sigil: $
    do
    $(let
      out2 = { [{7} { wf} {^#@} {"ewgfw"}] }
      quoted_out2 = {$(quote [{7} { wf} {^#@} {"ewgfw"}] )}
    )
    let wf = 1;
    let out = $(array ith get head $(array ith remove head $out2));
    let out2 = $(array ith get 2 $(array ith remove 2 $out2));
    let quoted_out = $(array q ith get head $(array q ith remove head $quoted_out2));
    let quoted_out2 = $(array q ith get 2 $(array q ith remove 2 $quoted_out2));
  };
  assert_eq!(out, 1);
  assert_eq!(out2, "ewgfw");
  assert_eq!(quoted_out, 1);
  assert_eq!(quoted_out2, "ewgfw");
}

#[test]
fn array_ith_insert_test() {
  do_with_in!{
    sigil: $
    do
    $(var
      out2 = { $(array ith insert 2 {55} $(array ith insert head {'4'} [{7} { wf} {^#@} {"ewgfw"}])) }
      quoted_out2 = { $(array q ith insert 2 $(quote {55}) $(array q ith insert head $(quote {'4'}) $(quote [{7} { wf} {^#@} {"ewgfw"}]))) }
    )
    let wf = 1;
    let out = $(array ith get head $(array ith insert head {'4'} $out2));
    let out2 = $(array ith get 2 $(array ith remove 2 $out2));
    let out3 = $(array length $out2);
    let out4 = $(array length $(array ith insert tail {8} $out2));
    let out5 = $(array ith get tail $(array ith insert tail {8} $out2));
    let out6 = $(array ith get -2 $(array ith insert -2 {8} $out2));
    let out7 = $(array ith get tail $(array ith insert -2 {8} $out2));
    let quoted_out = $(array q ith get head $(array q ith insert head $(quote {'4'}) $quoted_out2));
    let quoted_out2 = $(array q ith get 2 $(array q ith remove 2 $quoted_out2));
    let quoted_out3 = $(array q length $quoted_out2);
    let quoted_out4 = $(array q length $(array q ith insert tail $(quote {8}) $quoted_out2));
    let quoted_out5 = $(array q ith get tail $(array q ith insert tail $(quote {8}) $quoted_out2));
    let quoted_out6 = $(array q ith get -2 $(array q ith insert -2 $(quote {8}) $quoted_out2));
    let quoted_out7 = $(array q ith get tail $(array q ith insert -2 $(quote {8}) $quoted_out2));
  };
  assert_eq!(out, '4');
  assert_eq!(out2, 1);
  assert_eq!(out3, 6);
  assert_eq!(out4, 7);
  assert_eq!(out5, 8);
  assert_eq!(out6, 8);
  assert_eq!(out7, "ewgfw");
  assert_eq!(quoted_out, '4');
  assert_eq!(quoted_out2, 1);
  assert_eq!(quoted_out3, 6);
  assert_eq!(quoted_out4, 7);
  assert_eq!(quoted_out5, 8);
  assert_eq!(quoted_out6, 8);
  assert_eq!(quoted_out7, "ewgfw");
}

#[test]
fn withSigil_test1() {
  do_with_in!{
    sigil: $
    do
    $(let a = {1})
    let a = $(withSigil # #(arithmetic i8 #a + 3));
    let b = $(withSigil ~ ~(arithmetic i8 (~a + 1) * ~(withSigil % %(arithmetic i8 4 - %a))));
  }
  assert_eq!(a, 4);
  assert_eq!(b, 6);
}

#[test]
fn import_test1() {
  do_with_in!{
    file: "do_with_in_internal_macros/tests/do_with_in_test.rs"
    sigil: $
    do
    $(import "import.$")
    let $b = $a;
  };
  assert_eq!(c, 1);
}

#[test]
fn import_test2() {
  do_with_in!{
    file: "do_with_in_internal_macros/tests/do_with_in_test.rs"
    sigil: $
    do
    $(import "import.$")
    $(withSigil % %(import "import.%"))
    let $b = $a;
    let $s = $r;
  };
  assert_eq!(c, 1);
  assert_eq!(a, 1);
}

#[test]
fn import_test3() {
  do_with_in!{
    sigil: $
    do
    $(import Base "do_with_in_internal_macros" "tests" "import.$")
    
    let $b = $a;
  };
  assert_eq!(c, 1);
}

#[test]
fn import_test4() {
  do_with_in!{
    sigil: $
    do
    $(import Base "import_base_test.$")
    
    let $b = $a;
  };
  assert_eq!(c, 1);
}

#[test]
fn import_test5() {
  do_with_in!{
    sigil: $
    do
    $(import Base "import_base_test2.$")
    let $z = $c;
  };
  assert_eq!(twelve, 12);
}

#[test]
fn fn_test() {
  do_with_in!{
    sigil: $
    do
    $(fn blah (a b, c d=3, _ e={let c}) { $0 = $b + $d; })
    //$(blah ({let mut d}, a=3, c=4))
    let a = 1;
  };
  assert_eq!(a, 1);
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


