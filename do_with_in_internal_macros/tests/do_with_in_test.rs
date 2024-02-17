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
    let m = $(concat "The number (mod 3): " $(arithmetic f64 ($z) % 3));
    let shl = $(arithmetic u64 10 < 2);
    let shr = $(arithmetic u64 10 > 2);
    let and = $(arithmetic u64 22 & 34);
    let xor = $(arithmetic u64 22 ^ 34);
    let  or = $(arithmetic u64 22 | 34);
    let not = $(arithmetic u64 not 22);
    let no2 = $(arithmetic i8 not 22);
  }
  assert_eq!(x, 3);
  assert_eq!(n, "The number: 4.8f64");
  assert_eq!(m, "The number (mod 3): 1.7999999999999998f64");
  assert_eq!(shl, 2);
  assert_eq!(shr, 40);
  assert_eq!(and, 2);
  assert_eq!(xor, 52);
  assert_eq!(or,  54);
  assert_eq!(not, 18446744073709551593);
  assert_eq!(no2, -23);
}

#[test]
fn arithmetic_number_parsing_test1() {
  do_with_in!{
    sigil: $
    do
    assert_eq!($(arithmetic u64 1 + 2 + 3), 6u64);
    assert_eq!($(arithmetic f64 1 + 2 + 3), 6f64);
    assert_eq!($(arithmetic f64 1. + 2. + 3.), 6f64);
    assert_eq!($(arithmetic f64 1.1 + 2.2 + 3.3), 6.6f64);
    assert_eq!($(arithmetic i64 (0 - 1) + 2 + 3), 4i64);
    //let f = $(arithmetic u64 -1 + 2 + 3);
    //assert_eq!(f, 4u64);
    // -> shoould get a compiler error: Tried to negate an unsigned number of type u64
    assert_eq!($(arithmetic i64 -1 + 2 + 3), 4i64);
    assert_eq!($(arithmetic f64 -1 + 2 + 3), 4f64);
    let f = $(arithmetic f64 (-1.0) + (-2.1) + 3.2);
    assert_eq!(f, (-1.0) + (-2.1) + 3.2);
    let g = $(arithmetic f64 (-1.0) + -2.1 + 3.2);
    assert_eq!(g, (-1.0) + -2.1 + 3.2);
    let h = $(arithmetic f64 -1.0 + -2.1 + 3.2);
    assert_eq!(h, -1.0 + -2.1 + 3.2);
    //let h = $(arithmetic f64 -(-1.0 + -2.1 + 3.2));
    //assert_eq!(h, -(-1.0 + -2.1 + 3.2));
  }
}

#[test]
fn arithmetic_sizes_test() {
  do_with_in!{
    sigil: $
    do
    let size_u8_u64 = $(arithmetic u64 size_of u8);
    let size_u8_i8 = $(arithmetic i8 size_of u8);
    let size_usize_isize = $(arithmetic isize size_of usize);
    let size_usize_isize_bits = $(arithmetic isize 8 * (size_of usize));
  }
  assert_eq!(size_u8_u64, 1u64);
  assert_eq!(size_u8_i8, 1i8);
  assert_eq!(size_usize_isize, 8isize);
  assert_eq!(size_usize_isize_bits, 64isize);
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
fn basic_logic_string_equality_test() {
  do_with_in!{
    sigil: #
    do
    let aa = #(logic eq_str "a" "a");
    let ab = #(logic eq_str "a" "b");
    let bb = #(logic eq_str "b" "b");
    let cc = #(logic eq_str "thing" "thing");
    #(let dd = { "d" "d" })
    #(let de = { "d" "e" })
    let dd = #(logic eq_str #dd);
    let de = #(logic eq_str #de);
  }
  assert_eq!(aa, true);
  assert_eq!(ab, false);
  assert_eq!(bb, true);
  assert_eq!(cc, true);
  assert_eq!(dd, true);
  assert_eq!(de, false);
}

#[test]
fn combination_logic_test() {
  do_with_in!{
    sigil: #
    do
    let aat = #(logic (eq_str "a" "a") & true);
    let aaf = #(logic (eq_str "a" "a") & false);
    let ab1 = #(logic (eq_str "a" "b") | (eq_str "c" "d"));
    let ab2 = #(logic (eq_str "a" "b") & (eq_str "c" "d"));
    let ab3 = #(logic (eq_str "a" "b") | (eq_str "c" "c"));
    let ab4 = #(logic (eq_str "a" "b") & (eq_str "c" "c"));
    let ab5 = #(logic (eq_str "a" "a") & (eq_str "c" "c"));
    let ab6 = #(logic ! (eq_str "qa" "qb"));
    let ab7 = #(logic ! (eq_str "qa" "qa"));
    let bb = #(logic (2 > 1) & (eq_str "b" "b"));
    let cc = #(logic (eq_str "thing" "thing") & (6 < 7));
    #(let dd = { "d" "d" })
    #(let de = { "d" "e" })
    #(let num1 = { 5 })
    #(let num2 = { 7 })
    let dd1 = #(logic (eq_str #dd) & (#num1 > #num2));
    let dd2 = #(logic (eq_str #dd) & (#num1 < #num2));
    let de1 = #(logic (eq_str #de) & (#num1 > #num2));
    let de2 = #(logic (eq_str #de) & (#num1 < #num2));
  }
  assert_eq!(aat, true);
  assert_eq!(aaf, false);
  assert_eq!(ab1, false);
  assert_eq!(ab2, false);
  assert_eq!(ab3, true);
  assert_eq!(ab4, false);
  assert_eq!(ab5, true);
  assert_eq!(ab6, true);
  assert_eq!(ab7, false);
  assert_eq!(bb, true);
  assert_eq!(cc, true);
  assert_eq!(dd1, false);
  assert_eq!(dd2, true);
  assert_eq!(de1, false);
  assert_eq!(de2, false);
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
fn array_each_test() {
  do_with_in!{
    sigil: $
    do
    $(array each if [{(true) {let f = 3;} {let f = 4;}} {(false) {let g = 3;} {let g = 4;}} {($(logic 7 > 3)) {let h = 3;} {let h = 4;}} {($(logic 7 < 3)) {let i = 3;} {let i = 4;}} ])
  };
  do_with_in!{
    sigil: #
    do
    #(array each if [{(true) {let j = 3;} {let j = 4;}} {(false) {let k = 3;} {let k = 4;}} {(#(logic 7 > 3)) {let l = 3;} {let l = 4;}} {(#(logic 7 < 3)) {let m = 3;} {let m = 4;}} ])
  };
  assert_eq!(f, 3);
  assert_eq!(g, 4);
  assert_eq!(h, 3);
  assert_eq!(i, 4);
  assert_eq!(j, 3);
  assert_eq!(k, 4);
  assert_eq!(l, 3);
  assert_eq!(m, 4);
}

#[test]
fn array_map_test() {
  do_with_in!{
    sigil: $
    do
    $(let
      insert = {{[{[2] [a] [u64]}] [{[3] [b] [i32]}] [{[0] [c] [u8]}] }}
      sectionf = {{fn $(string_to_ident $(concat "f_" $(arithmetic u64u 2 * $(array ith get 0 $test))))($(array ith get 1 $test): $(array ith get 2 $test)) -> $(array ith get 2 $test) { $(array ith get 1 $test) * $(array ith get 0 $test) } }}
      sectionv = {{let $(string_to_ident $(concat "v_" $(array ith get 0 $test))) = $(string_to_ident $(concat "f_" $(arithmetic u64u 2 * $(array ith get 0 $test))))($(array ith get 0 $test) + 1); }})
    $(array map true test $sectionf $insert)
    $(array map true test $sectionv $insert)
  };
  assert_eq!(f_0(1), 0);
  assert_eq!(f_4(1), 2);
  assert_eq!(f_6(1), 3);
  assert_eq!(v_0, 0);
  assert_eq!(v_2, 6);
  assert_eq!(v_3, 12);
}

#[test]
fn fn_test() {
  do_with_in!{
    sigil: $
    do
    $(fn blah (a b, c d=3, _ e={let c}) { $0 = $b + $d; })
    //$(blah ({let mut d}, a=3, c=4))
    let a = 1;
    $(runMarkers Base "do_with_in_internal_macros" "tests" "do_with_in_test.rs")
    $(runMarkers Base "do_with_in_internal_macros" "tests" "do_with_in_test.rs" => "foo")
  };
  assert_eq!(a, 1);
}

#[test]
fn mk_test() {
  do_with_in!{
    sigil: $
    do
    $(mk blah
        $1 = $2 + $3;)
    $(blah {let mut d} 3 4)
    d += 1;
  };
  assert_eq!(d, 8);
}

#[test]
fn mk_test2_stalls() {
  #[derive(Clone, Copy, Debug)]
  pub struct Mem {
    pub mem: [u8; 512],
    pub stalls: [bool; 512],
  }
  pub type Addr = usize;
  pub type Imm8 = u8;
  pub fn stall(addr: Addr, it: &Mem) -> bool {
    it.stalls[addr]
  }
  pub mod chip {
    pub mod Pipeline {
      pub mod MainDecode {
        #[derive(Clone, Copy, Debug, PartialEq, Eq)]
        pub enum Instruction {
          Nop(Instructions::Nop),
          AddU(Instructions::AddU),
        }
        pub mod Instructions {
          #[derive(Clone, Copy, Debug, PartialEq, Eq)]
          pub struct Nop {}

          #[derive(Clone, Copy, Debug, PartialEq, Eq)]
          pub struct AddU {
            pub len: u8, pub l: usize, pub r: usize, pub out: usize,
          }
        }
      }
    }
  }
  type Progress = u32;

  #[derive(Clone, Debug, PartialEq, Eq)]
  enum Status {
    Blocked(chip::Pipeline::MainDecode::Instruction, Vec<Addr>),
    Running(chip::Pipeline::MainDecode::Instruction, Progress),
  }
  do_with_in!{
    sigil: $
    do
    $(mk stall
        $instruction_location::$instruction_enum::$1($instruction_location::$instruction_structs::$1{$2}) => {
          let mut blocked: Vec<Addr> = Vec::new();
          $(let arms = {{if stall($test, mem) {
            blocked.push($test);
          }}})
          $(array map true test $arms $3)
          if blocked.len() > 0 {
            Status::Blocked(inst, blocked)
          } else {
            Status::Running(inst, 0)
          }
        },
      )
    $(let instruction_location = {chip::Pipeline::MainDecode})
    $(let instruction_enum = {Instruction})
    $(let instruction_structs = {Instructions})
    fn check_stalls(inst: chip::Pipeline::MainDecode::Instruction, mem: &Mem) -> Status {
      match inst {
        $(stall Nop {} {{}})
        $(stall AddU {len, l, r, out} {{[l] [r]}})
      }
    }
  };
  let mem = Mem { mem: [0u8; 512], stalls: [false; 512], };
  let mut mem2 = mem.clone();
  mem2.stalls[3] = true;
  let mem2 = mem2.clone();
  let inst1 = chip::Pipeline::MainDecode::Instruction::Nop(chip::Pipeline::MainDecode::Instructions::Nop{});
  let inst2 = chip::Pipeline::MainDecode::Instruction::AddU(chip::Pipeline::MainDecode::Instructions::AddU{len: 0, l: 1, r: 2, out: 3});
  let inst3 = chip::Pipeline::MainDecode::Instruction::AddU(chip::Pipeline::MainDecode::Instructions::AddU{len: 0, l: 2, r: 3, out: 4});
  let stalls = [check_stalls(inst1, &mem), check_stalls(inst2, &mem),  check_stalls(inst3, &mem), check_stalls(inst1, &mem2), check_stalls(inst2, &mem2), check_stalls(inst3, &mem2)];
  assert_eq!(stalls, [Status::Running(inst1, 0), Status::Running(inst2, 0), Status::Running(inst3, 0), Status::Running(inst1, 0), Status::Running(inst2, 0), Status::Blocked(inst3, vec!(3)), ]);
}

#[test]
fn mk_test_noclobber_nested() {
  do_with_in!{
    sigil: $
    do
    let mut g = 4;
    $(mk blah
        $(run $1) = $(run $2) + $(run $3))
    $(blah {let mut d} {{$(blah g 1 {2; g})}} 4);
    $(mk simple $1 $3 $2)
    $(blah {$(simple let f mut)} g d);
    d += 1;
  };
  assert_eq!(d, 8);
  assert_eq!(f, 10);
}

#[test]
fn basic_marker_test() {
  do_with_in!{
    sigil: $
    do
    $(marker =>
      $(let x = { 3 })
      $(mk foo
          let $1 = $x * $2;))
    $(marker "first test" =>
      $(let x = { 4 })
      $(mk foo
          let $1 = $x * $2;))
    $(marker "second test" =>
      $(let x = { 5 })
      $(mk foo
          let $1 = $x + $2;))
    let g = 4;
  };
  assert_eq!(g, 4);
}

#[test]
fn basic_runMarker_test() {
  do_with_in!{
    sigil: $
    do
    $(runMarkers Base "do_with_in_internal_macros" "tests" "do_with_in_test.rs")
    $(foo g 2)
  }
  assert_eq!(g, 6);
}

#[test]
fn basic_runMarker_test2() {
  do_with_in!{
    sigil: $
    do
    $(runMarkers Base "do_with_in_internal_macros" "tests" "do_with_in_test.rs" => "first test")
    $(foo g 2)
  }
  assert_eq!(g, 8);
}

#[test]
fn basic_runMarker_test3() {
  do_with_in!{
    sigil: $
    do
    $(runMarkers Base "do_with_in_internal_macros" "tests" "do_with_in_test.rs" => "second test")
    $(foo g 2)
  }
  assert_eq!(g, 7);
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


