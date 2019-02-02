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
    t "less_1" "1 < 2" "true";
    t "less_2" "1 < 0" "false";

];;

let print_tests = [
	t "print_1" "print(41)" "41\n41";
	t "print_2" "print(true)" "true\ntrue";

];;

let all_tests = 
  number_tests @
  boolean_tests @
  prim1_tests @
  prim2_tests @
  print_tests
;;

let suite =
"suite">::: all_tests
;;

let () =
  run_test_tt_main suite
;;
