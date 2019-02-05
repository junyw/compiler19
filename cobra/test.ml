open Compile
open Runner
open Printf
open OUnit2

let t name program expected = name>::test_run program name expected;;
let te name program expected = name>::test_err program name expected;;

let number_tests = [
  t "number_1" "41" "41";
  t "number_2" "0" "0";
  t "number_3" "-41" "-41";
  t "number_4" "1073741823" "1073741823";
  (* More tests here *)
];;
let arithmetic_tests = [
  t "plus_1" "1 + 2" "3";
  t "plus_2" "11 + 23" "34";
  t "plus_3" "1073741823 + 0" "1073741823";
  t "minus_2" "1 - 2" "-1";
  t "arith_3" "1 * 2" "2";
  t "arith_4" "-1 * 2" "-2";
  t "arith_5" "12 * 34" "408";
  t "times_1" "1073741823 * 1" "1073741823";
  t "times_2" "1 * 1073741823" "1073741823";
  
  (* errors *)
  te "plus_error_1" "true + 1" "Error: arithmetic expected a number";
  te "plus_error_2" "1 + true" "Error: arithmetic expected a number";
  te "minus_error_1" "false - 1" "Error: arithmetic expected a number";
  te "minus_error_2" "1 - false" "Error: arithmetic expected a number";
  te "times_error_1" "1 * false" "Error: arithmetic expected a number";
  te "times_error_2" "true * 0" "Error: arithmetic expected a number";

];;
let overflow_tests = [
  te "overflow_1" "1073741824" "Compile error: Compile-time integer overflow";
  te "overflow_2" "add1(1073741823)" "Error: Integer overflow";
  te "overflow_3" "sub1(-1073741824)" "Error: Integer overflow";
  te "overflow_4" "1073741800 + 100" "Error: Integer overflow";
  te "overflow_5" "1 - 1073741820 - 10" "Error: Integer overflow";
  te "overflow_6" "10737418 * 120" "Error: Integer overflow";

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
  t "isbool_1" "isbool(true)" "true";
  t "isbool_2" "isbool(false)" "true";
  t "isbool_3" "isbool(1)" "false";
  t "not_1" "!(true)" "false";
  t "not_2" "!(false)" "true";
  t "prim1_1" "let x = if 1 + 3 >= 4: 10 else: false in isbool(x)" "false";
  t "prim1_2" "let x = if 1 + 3 > 4: 10 else: false in isbool(x)" "true";

  (* errors *)
  te "add1_error" "add1(true)" "Error: arithmetic expected a number";
  te "sub1_error" "sub1(false)" "Error: arithmetic expected a number";
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
  t "eq_4" "true == true" "true";
  t "eq_5" "false == true" "false";
  t "eq_6" "true == 1" "false";
  t "eq_7" "let x = 1 in x == 1" "true";
  t "eq_8" "let x = true in x == (1 >= 1)" "true";

  (* errors *)
  te "logic_error_1" "1 && true" "Error: logic expected a boolean, but got 1";
  te "logic_error_2" "false && 1" "Error: logic expected a boolean, but got 1";
  te "logic_error_3" "10 || true" "Error: logic expected a boolean, but got 10";
  te "logic_error_4" "true || 0" "Error: logic expected a boolean, but got 0";
  te "logic_error_5" "1 || 2" "Error: logic expected a boolean, but got 1";
  te "compare_error_1" "true > 1" "Error: comparison expected a number";
  te "compare_error_2" "1 > false" "Error: comparison expected a number";
  te "compare_error_3" "1 >= false" "Error: comparison expected a number";
  te "compare_error_4" "true > 0" "Error: comparison expected a number";
  te "compare_error_5" "1 < false" "Error: comparison expected a number";
  te "compare_error_6" "1 <= false" "Error: comparison expected a number";

];;

let print_tests = [
  t "print_1" "print(41)" "41\n41";
  t "print_2" "print(true)" "true\ntrue";
  t "print_3" {| let x = 1 in
                       let y = print(x + 1) in
                           print(y + 2) |}
  "2\n4\n4";
  t "print_4" "let x = (1 == 2) in print(x)" "false\nfalse";
  t "print_5" "print(1 == 2)" "false\nfalse";
];;
let let_tests = [
  t "let_1" "let x = 1 in x" "1";
  t "let_2" "let x = (1 == 2) in x" "false";
  t "let_3"  
  {| let x = true in
         let y = !(x) && x in
             y
  |} "false";
  t "let_4" 
  {| let x = 10 in
         let y = (if x >= (5 + 4): x + 3 else: false) in 
             isnum(x) && isnum(y)
  |} "true";

];;

let if_tests = [
  t "if_1" "if true: 1 else: 2" "1";
  t "if_2" "if false: 1 else: 2" "2";
  t "if_3" "if 3 > 2: 1 else: 2" "1";
  t "if_4" "if !(2 == (1 + 1)): 1 else: 2" "2";
  t "if_5" "if (let x = true in x): 1 else: 2" "1";
  t "if_6" "let x = 1 in if x > 0: 1 else: 2" "1";
  (* errors *)
  te "if_error_1" "if 54: true else: false" "Error: if expected a boolean";
  te "if_error_2" "let x = 1 in (if x: true else: false)" "Error: if expected a boolean";
  te "if_error_3" "if (let x = 1 in x): true else: false" "Error: if expected a boolean";
];;

let all_tests = 
  number_tests @
  arithmetic_tests @
  overflow_tests @
  boolean_tests @
  prim1_tests @
  prim2_tests @
  print_tests @
  let_tests @
  if_tests
;;

let suite =
"suite">::: all_tests
;;

let () =
  run_test_tt_main suite
;;
