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
  te "runtime_overflow_1" "add1(1073741823)" "Error: Integer overflow";
  te "runtime_overflow_2" "10737418 * 120" "Error: Integer overflow";
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
t "fun_1" {|
	def Max(x, y):
	    if(x > y): x else: y
	Max(1, 2) * Max(2, 1)
|} "4";

t "fun_2" {|
	def NAND(a, b):
		!(a && b)
	def XOR(a, b):
		NAND(NAND(a, NAND(a, b)), NAND(b, NAND(a, b)))
	let a = print(XOR(true, true)) in 
	let b = print(XOR(true, false)) in
	let c = print(XOR(false, true)) in
		print(XOR(false, false))
|} "false\ntrue\ntrue\nfalse\nfalse";

t "fun_3" {|
	def q(x):
		let a = 1, b = -1, c = -2 in
			(a * x * x) + (b * x) + c
	(q(0) == -2) && (q(-1) == 0) && (q(2) == 0)
|} "true";

];;

let recursive_tests = [
t "recursive_1" {| 
    def factorial(n):
		if (n == 0): 1 else: n * factorial(n - 1)
	factorial(6) |} "720";
t "recursive_2" {|
	def fib(n):
		if(n == 1): 1 
	    else: 
	    	if(n == 2): 1 
	        else: fib(n - 1) + fib(n - 2)
	fib(6) |} "8";
];;

let arity_tests = [
t "arity_0" {| def f():
                 10
                 f() |} "10";
t "arity_1" {| def f(x, y, z):
                 (x * x) + (y * y) + (z * z)
             f(1, 2, 3)|} "14";
t "arity_2" {| def f(a, b, c, d):
                 (a * c) - (b * d) 
             f(1, 2, 3, 4)|} "-5";
t "arity_3" {| def f(a, b, c, d, e):
                 e
             f(1, 2, 3, 4, 5)|} "5";
t "arity_4" {| def f(a, b, c, d, e, f):
                 f
             f(1, 2, 3, 4, 5, 6)|} "6";
t "arity_5" {| def f(a, b, c, d, e, f, g):
                 g
             f(1, 2, 3, 4, 5, 6, 7)|} "7";
];;

let well_formedness_tests = [
	te "duplicate_1" {| def f(x, x):
						 x
						0  |}  "The identifier x, redefined at <duplicate_1, 1:10-1:11>";
	te "duplicate_2" {| def f(x):
						 x
						def f(y):
						 y
						0  |}  "The identifier f, redefined at <duplicate_2, 3:6-4:8>";
	te "duplicate_3" {| let x = 1, x = 2 in x |} 
		             "The identifier x, redefined at <duplicate_3, 1:12-1:13>";
	te "duplicate_4" {| let x = (let y = 1, y = 2 in y) in x |} 
		             "The identifier y, redefined at <duplicate_4, 1:21-1:22>";
	te "unbound_1" {| x |}  "The identifier x, used at <unbound_1, 1:1-1:2>, is not in scope";
	te "unbound_2" {| def f(x):
	                      y
	                  0 |}  "The identifier y, used at <unbound_2, 2:23-2:24>, is not in scope";
    te "overflow_1" "1073741824" "The number literal 1073741824, used at <overflow_1, 1:0-1:10>, is not supported in this language";

];;
let all_tests = 
  expr_tests @
  function_tests @
  recursive_tests @
  arity_tests @
  well_formedness_tests
;;

let suite =
"suite">::: all_tests
;;

let () =
  run_test_tt_main suite
;;
