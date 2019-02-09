open Compile
open Runner
open Printf
open OUnit2
open Pretty
open Exprs
       
let is_osx = Conf.make_bool "osx" false "Set this flag to run on osx";;

let t name program expected = name>::test_run program name expected;;

let ta name program expected = name>::test_run_anf program name expected;;

let te name program expected_err = name>::test_err program name expected_err;;

let tvg name program expected = name>::test_run_valgrind program name expected;;
  
let tanf name program expected = name>::fun _ ->
  assert_equal expected (anf (tag program)) ~printer:string_of_aprogram;;

let teq name actual expected = name>::fun _ ->
  assert_equal expected actual ~printer:(fun s -> s);;

let expr_tests = [
  (* arithmetic tests *)
  t "expr_1" "3" "3";
  t "expr_2" "1 + 2" "3";
  t "expr_3" "1 * 2 + 3" "5";
  t "times_1" "1073741823 * 1" "1073741823";
  te "minus_error_2" "1 - false" "Error: arithmetic expected a number";
  te "times_error_1" "1 * false" "Error: arithmetic expected a number";
  te "overflow_1" "1073741824" "Compile error: Compile-time integer overflow";
  te "overflow_2" "add1(1073741823)" "Error: Integer overflow";
  te "overflow_6" "10737418 * 120" "Error: Integer overflow";
  t "add1_1" "add1(1)" "2";
  t "sub1_1" "sub1(1)" "0";
  t "isnum_1" "isnum(1)" "true";
  t "isnum_2" "isnum(true)" "false";
  t "prim1_1" "let x = if 1 + 3 >= 4: 10 else: false in isbool(x)" "false";
  t "prim1_2" "let x = if 1 + 3 > 4: 10 else: false in isbool(x)" "true";
  te "add1_error" "add1(true)" "Error: arithmetic expected a number";
  
  (* logic tests *)
  t "isbool_1" "isbool(true)" "true";
  t "isbool_2" "isbool(false)" "true";
  t "isbool_3" "isbool(1)" "false";
  t "not_1" "!(true)" "false";
  t "not_2" "!(false)" "true";
  t "and_1" "true && true" "true";
  t "or_1" "true || true" "true";
  t "greater_1" "2 > 1" "true";
  t "greaterEq_1" "2 >= 1" "true";
  t "less_1" "1 < 2" "true";
  t "less_2" "1 < 0" "false";
  t "lessEq_1" "1 <= 2" "true";
  t "eq_1" "1 == 1" "true";
  t "eq_2" "1 == 0" "false";  
  (* errors *)
  te "not_error_1" "!(3)" "Error: logic expected a boolean, but got 3";
  te "logic_error_1" "1 && true" "Error: logic expected a boolean, but got 1";
  te "logic_error_2" "false && 1" "Error: logic expected a boolean, but got 1";
  te "compare_error_1" "true > 1" "Error: comparison expected a number";
  
  (* print tests *)
  t "print_1" "print(41)" "41\n41";
  t "print_2" "print(true)" "true\ntrue";

  (* let tests *)
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

  (* if tests *)
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

let function_tests = [
t "fun_1" {| def f(x):
                 x
                 1|} "";

(*t "test_1" {| def f(x, y):
                  x + y
              f(1, 2) |}
              "3";*)

];;
let all_tests = 
  (*expr_tests @*)
  function_tests
;;

let suite =
"suite">::: all_tests
;;

let () =
  run_test_tt_main suite
;;
