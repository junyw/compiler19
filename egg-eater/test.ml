open Compile
open Runner
open Printf
open OUnit2
open Pretty
open Exprs
open Phases
open Assembly
open Errors
open Inference
open ExtLib

let is_osx = Conf.make_bool "osx" false "Set this flag to run on osx";;

let t name program expected = name>::test_run program name expected;;

let ta name program expected = name>::test_run_anf program name expected;;

let te name program expected_err = name>::test_err program name expected_err;;

let tvg name program expected = name>::test_run_valgrind program name expected;;
  
let tanf name program expected = name>::fun _ ->
  assert_equal expected (anf (tag program)) ~printer:string_of_aprogram;;

let teq name actual expected = name>::fun _ ->
  assert_equal expected actual ~printer:(fun s -> s);;

let t_any name value expected = name>::
  (fun _ -> assert_equal expected value ~printer:dump);;

(* well-formedness tests *)
let wf_errs = [
  te "duplicate_1" {| def f(x, x):
                          x
                      0  |}  
      "The identifier x, redefined at <duplicate_1, 1:10-1:11>";
  
  te "duplicate_2" {| let x = 1, x = 2 in x |} 
     "The identifier x, redefined at <duplicate_2, 1:12-1:13>";
  
  te "duplicate_3" {| let x = (let y = 1, y = 2 in y) in x |} 
     "The identifier y, redefined at <duplicate_3, 1:21-1:22>";

  te "fun_duplicate_1" {| def foo(x): 
                              x
                          def foo(y):
                              y
                          1  |} 
     "The function name foo, redefined at <fun_duplicate_1, 3:26-4:31>, duplicates one at <fun_duplicate_1, 1:1-2:31>";
  
  te "unbound_1" {| x |}  
     "The identifier x, used at <unbound_1, 1:1-1:2>, is not in scope";
  
  te "unbound_2" {| def f(x):
                        y
                    0 |}  
     "The identifier y, used at <unbound_2, 2:24-2:25>, is not in scope";
 
  te "overflow_1" "1073741824" 
     "The number literal 1073741824, used at <overflow_1, 1:0-1:10>, is not supported in this language";

  te "unbound_fun_1" {| f(1) |} 
     "The function name f, used at <unbound_fun_1, 1:1-1:5>, is not in scope";
  
  te "arity_mismatch_1" {| def f(x, y):
                                x + y
                            f(1) |} 
     "The function called at <arity_mismatch_1, 3:28-3:32> expected an arity of 2, but received 1 arguments";

  (* the following program should report 3 errors *)
  te "errors_1" {| def f(x, x):
                       y
                   f(1) |} 
  "The identifier x, redefined at <errors_1, 1:10-1:11>, duplicates one at <errors_1, 1:7-1:8>
The identifier y, used at <errors_1, 2:23-2:24>, is not in scope
The function called at <errors_1, 3:19-3:23> expected an arity of 2, but received 1 arguments";
  
];;

let runtime_errs = [
  (* integer overflow *)
  te "runtime_overflow_1" "add1(1073741823)" "Error: Integer overflow";
  te "runtime_overflow_2" "10737418 * 120" "Error: Integer overflow";

];;

let expr_tests = [
  (* arithmetic tests *)
  t "expr_1" "3" "3";
  t "expr_2" "1 + 2" "3";
  t "expr_3" "1 * 2 + 3" "5";
  t "times_1" "1073741823 * 1" "1073741823";
  t "add1_1" "add1(1)" "2";
  t "sub1_1" "sub1(1)" "0";
  t "isnum_1" "isnum(1)" "true";
  t "isnum_2" "isnum(true)" "false";
  
  (* logic tests *)
  t "isbool_1" "isbool(true)" "true";
  t "isbool_2" "isbool(false)" "true";
  t "isbool_3" "isbool(1)" "false";
  t "not_1" "!(true)" "false";
  t "not_2" "!(false)" "true";
  t "and_1" "true && true" "true";
  t "or_1" "true || true" "true";
  t "greater_1" "2 > 1" "true";
  t "greater_2" "2 > -1" "true";
  t "greater_3" "1 > 1" "false";

  t "greaterEq_1" "2 >= 1" "true";
  t "less_1" "1 < 2" "true";
  t "less_2" "1 < 0" "false";
  t "lessEq_1" "1 <= 2" "true"; 
  t "eq_1" "1 == 1" "true";
  t "eq_2" "1 == 0" "false";  
  t "eq_3" "false == false" "true";

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
         let y = (if x >= (5 + 4): true else: false) in 
             isnum(x) && isnum(y)
  |} "false";

  (* let* semantics *)
  t "let_5" {| let x = 10, y = x * 2 in y |} "20";  

  (* if tests *)
  t "if_1" "if true: 1 else: 2" "1";
  t "if_2" "if false: 1 else: 2" "2";
  t "if_3" "if 3 > 2: 1 else: 2" "1";
  t "if_4" "if !(2 == (1 + 1)): 1 else: 2" "2";
  t "if_5" "if (let x = true in x): 1 else: 2" "1";
  t "if_6" "let x = 1 in if x > 0: 1 else: 2" "1";
];;

let renaming_tests = [
   t "rename_1" {| (let x = 1 in x) + (let x = 2 in x) |} "3";
   t "rename_2" {| def foo(x : Int) -> Int:
                       x + (let x = 1 in x) + (let x = 2 in x)
                    foo(3) |} "6";
];;


let typed_fun_tests = [
  t "typed_fun_1" {|
    def typed_max(x: Int, y: Int) -> Int:
        if(x > y): x else: y

    typed_max(1, 2) * typed_max(2, 1)
  |} "4";

  t "typed_fun_2" {|
    def typed_nand(a: Bool, b: Bool) -> Bool:
      !(a && b)
    and 
    def typed_xor(a: Bool, b: Bool) -> Bool:
      typed_nand(typed_nand(a, typed_nand(a, b)), 
                 typed_nand(b, typed_nand(a, b)))

    let a = print(typed_xor(true, true)) in 
    let b = print(typed_xor(true, false)) in
    let c = print(typed_xor(false, true)) in
      print(typed_xor(false, false))
  |} "false\ntrue\ntrue\nfalse\nfalse";

  t "typed_fun_3" {|
    def typed_q(x: Int) -> Int:
      let a = 1, b = -1, c = -2 in
        (a * x * x) + (b * x) + c

    (typed_q(0) == -2) && (typed_q(-1) == 0) && (typed_q(2) == 0)
  |} "true";

];;

let fun_tests = [
  t "funx_1" {|
    def foo1(x):
      x + 6

    foo1(38)
  |} "44";
  
  t "funx_02" {|
    def foo2(x):
      let y = 6 in x + y

    foo2(38)
  |} "44";

  t "funx_03" {|
    def foo3(x):
      x == 1

    foo3(38)
  |} "false";

  t "fun_1" {|
    def max(x, y):
        if(x > y): x else: y

    max(1, 2) * max(2, 1)
  |} "4";

  t "fun_2" {|
    def nand(a, b):
      !(a && b)
    and
    def xor(a, b):
      nand(nand(a, nand(a, b)), nand(b, nand(a, b)))

    let a = print(xor(true, true)) in 
    let b = print(xor(true, false)) in
    let c = print(xor(false, true)) in
      print(xor(false, false))
  |} "false\ntrue\ntrue\nfalse\nfalse";

  t "fun_3" {|
    def q(x):
      let a = 1, b = -1, c = -2 in
        (a * x * x) + (b * x) + c

    (q(0) == -2) && (q(-1) == 0) && (q(2) == 0)
  |} "true";

  t "fun_4" {|
    def mult(x, y):
      x * y
    and 
    def square(x):
      mult(x, x)
    square(3)
  |} "9";

  t "id_1" {|
    def id(x) : let y = x in x
    id(true)
  |} "true";

  t "fxyz" 
   {|
      def fxyz(x, y, z):
        if(id(x)): id(y)
        else: id(z)
      and 
      def id(x): 
        x

      fxyz(true, 4, 5)
   |} "4";

  t "f_boolint" {| def f_boolint(x, y):
                (x == true) && (y == 1)

             f_boolint(true, 1) |} "true";

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

  t "mutual_1" {|
    def is_even(n):
        if(n == 0): true
        else: is_odd(n - 1)
    and
    def is_odd(n):
        if(n == 0): false
        else: is_even(n - 1)

    is_even(4) && !(is_even(3)) && is_odd(5)
  |} "true";

  (* this function call would stack-overflow without tail-call optimization *)
(*  t "tail_1" {|
      def tail1(x, y):
        if x > 0: tail1(x - 1, y + 1)
        else: y

      tail1(1000000, 0)  |} "1000000";
*)
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

let type_expr_tests = [
  t "expr_add1" 
    "let x: Int = 1 in x" "1";

  te "expr_err_1" 
     "let x: Bool = 1 in x" 
     "Type error at expr_err_1, 1:4-1:11: expected Bool but got Int";

  te "expr_err_2" 
     "let x = 1, y: Bool = x in y" 
     "Type error at expr_err_2, 1:11-1:18: expected Bool but got Int";

];;


let language_tests = 
    expr_tests 
  @ renaming_tests
  @ typed_fun_tests
  @ fun_tests
  @ arity_tests
;;

let tuple_tests = [
  t "istuple_0" "let t = 1 in istuple(t)" "false";
  t "istuple_1" "let t = (1,) in istuple(t)" "true";
  t "tuple_0" "let t0 = () in t0" "()";
  t "tuple_1" "let t1 = (1,) in t1" "(1,)";
  t "tuple_2" "let t2 = (1,2) in t2" "(1,2)";
  t "tuple_3" "let t3 = (1,2,true) in t3" "(1,2,true)";
  t "tuple_4" "let t4 = (1,2,true,false) in t4" "(1,2,true,false)";
  
  t "tnested_0" {| let t1 = (1,2,3) in 
                      let t2 = (t1,4) in
                        t2[1 of 2] |} "4";

  t "tnested_1" "let t = (1,2,(3,)) in t" "(1,2,(3,))";
  t "tnested_2" "let t = (1,2,(4,3)) in t" "(1,2,(4,3))";
  t "tnested_3" {| let t0 = (4,3,2) in 
                     let t = (1,2,t0) in t |} "(1,2,(4,3,2))";
  
  t "tnested_get_1" {| let t = (1,2,(3,4,(5,6))) in 
                          t[2 of 3][2 of 3][0 of 2]|} "5";

  t "tuple_5" "let x = 1 in let t = (x, 2) in 1" "1";

  (* reference equality *)
  t "teq_1" "let t = (4, 5) in t == t" "true";

  t "tget_0" "let t1 = (1,2,3,4) in t1[0 of 4]" "1";
  t "tget_1" "let t1 = (1,2,3,4) in t1[1 of 4]" "2";
  t "tget_2" "let t1 = (1,2,3,4) in t1[2 of 4]" "3";
  t "tget_3" "let t1 = (1,2,3,4) in t1[3 of 4]" "4";
  t "tset_1" {| let t = (0,0,0) in
                    t[1 of 3 := 2] |} "(0,2,0)";


  t "tset_2" {| let three = (0, 0, 0) in
                  let _ = three[0 of 3 := 1][1 of 3 := 2][2 of 3 := 3] in
                    let pair = (0, 0) in
                      pair[0 of 2 := three[1 of 3 := 10]] |} "((1,10,3),0)";

  t "tset_3" {| let three = (0, 0, 0) in
                  three[0 of 3 := 1][1 of 3 := 2][2 of 3 := 3] |} "(1,2,3)";
  
  t "tprint_1" "print((4, (true, 3)))" "(4,(true,3))\n(4,(true,3))";

  t "link_1" {| def link(first, rest):
                    (first, rest)
                link(1, false) |} "(1,false)";
];;
let seq_tests = [
  t "blank_1" "let _ = 1 in 2" "2";
  t "seq_1" "let x = 1; 2 in x" "2";
  t "seq_2" "let t = (1, 2) in t[0 of 2 := 10]; (1, t)" "(1,(10,2))";
];;
let destructuring_tests = [
  t "des_1" "let (a, b, c) = (1, 2, 3) in b" "2";
  t "des_2" "let (_, b, c) = (1, 2, 3) in c" "3";
  t "des_3" "let ((x, y), b, c) = ((1, 2), 3, 4) in y" "2";
  t "des_4" "let (a, (b, (c, d))) = (1, (2, (3, 4))) in (d - c) * a" "1";

  t "des_fun_1" {| def add_pairs((x1, y1), (x2, y2)):
                       (x1 + x2, y1 + y2) 

                   add_pairs((1, 2), (3, 4)) |} "(4,6)";
  t "des_fun_2" {| def add_to_pairs((x1, y1), n):
                       (x1 + n, y1 + n) 

                   add_to_pairs((1, 2), -1) |} "(0,1)";
  t "des_fun_3" {| def reverse((x, (y, z))):
                        (z, (y, x))
                   reverse((1, (2, 3))) |} "(3,(2,1))";


];;

let all_tests = []
  @ wf_errs
  @ runtime_errs
  @ tuple_tests
  @ seq_tests
  @ destructuring_tests
  @ language_tests  
;;

let suite =
"suite">::: all_tests
;;


let () =
  run_test_tt_main suite
;;
