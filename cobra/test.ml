open Compile
open Runner
open Printf
open OUnit2

let t name program expected = name>::test_run program name expected;;
let te name program expected = name>::test_err program name expected;;

let forty = "let x = 40 in x"
let fals = "let x = false in x"
let tru = "let x = true in x"

(*let suite =
"suite">:::
 [
  t "forty" forty "40";
  t "fals" fals "false";
  t "tru" tru "true";
 ]
;;
*)
let number_tests = [
  t "number_1" "41" "41";
  t "number_2" "0" "0";
  t "number_3" "-41" "-41";
  (* More tests here *)
];;
let arithmetic_tests = [
  t "arith_1" "1 + 2" "3";
  t "arith_2" "1 - 2" "-1";
  t "arith_3" "1 * 2" "2";
  t "arith_4" "-1 * 2" "-2";
  t "arith_5" "12 * 34" "408";
];;
let boolean_tests = [
  t "boolean_1" "false" "false";
  t "boolean_2" "true" "true";

  (* More tests here *)

];;
let prim1_tests = [
	t "add1_1" "add1(1)" "2";
	t "sub1_1" "sub1(1)" "0";
	t "isnum_1" "isnum(1)" "true";
	t "isnum_2" "isnum(true)" "false";
	t "not_1" "!(true)" "false";
	t "not_2" "!(false)" "true";

];;
let prim2_tests = [
	t "and_1" "true && true" "true";
	t "and_2" "true && false" "false";
	t "and_3" "false && true" "false";
	t "and_4" "false && false" "false";
	t "or_1" "true || true" "true";
	t "or_2" "true || false" "true";
	t "or_3" "false || true" "true";
	t "or_4" "false || false" "false";
    t "greater_1" "2 > 1" "true";
    t "greater_2" "2 > 3" "false";
    t "greaterEq_1" "2 >= 1" "true";
    t "greaterEq_2" "0 >= 1" "false";
    t "greaterEq_3" "1 >= 1" "true";
    t "greaterEq_4" "-1 >= -1" "true";
    t "less_1" "1 < 2" "true";
    t "less_2" "1 < 0" "false";
    t "lessEq_1" "1 <= 2" "true";
    t "lessEq_2" "1 <= 0" "false";
    t "lessEq_3" "1 <= 1" "true";
    t "lessEq_4" "-1 <= -1" "true";
    t "eq_1" "1 == 1" "true";
    t "eq_2" "1 == 0" "false";
    t "eq_3" "-1 == -1" "true";
];;

let print_tests = [
	t "print_1" "print(41)" "41\n41";
	t "print_2" "print(true)" "true\ntrue";
	t "print_3" {| let x = 1 in
                       let y = print(x + 1) in
                           print(y + 2) |}
    "2\n4\n4";

];;

let if_tests = [
	t "if_1" "if true: 1 else: 2" "1";
	t "if_error_1" "if 54: true else: false" "should be error";

];;

let all_tests = 
  number_tests @
  arithmetic_tests @
  boolean_tests @
  prim1_tests @
  prim2_tests @
  print_tests @
  if_tests
;;

let suite =
"suite">::: all_tests
;;

let () =
  run_test_tt_main suite
;;
