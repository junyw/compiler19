open Compile
open Runner
open Printf
open OUnit2
open Pretty
open Exprs
open Phases
open Errors

let t name program input expected = name>::test_run [] input program name expected;;
let ta name program input expected = name>::test_run_anf [] input program name expected;;
let tgc name heap_size program input expected = name>::test_run [string_of_int heap_size] input program name expected;;
let tvg name program input expected = name>::test_run_valgrind [] input program name expected;;
let tvgc name heap_size program input expected = name>::test_run_valgrind [string_of_int heap_size] input program name expected;;
let terr name program input expected = name>::test_err [] input program name expected;;
let tgcerr name heap_size program input expected = name>::test_err [string_of_int heap_size] input program name expected;;
let tanf name program input expected = name>::fun _ ->
  assert_equal expected (anf (tag program)) ~printer:string_of_aprogram;;

let teq name actual expected = name>::fun _ ->
  assert_equal expected actual ~printer:(fun s -> s);;

let tfvs name program expected = name>::
  (fun _ ->
    let ast = parse_string name program in
    let anfed = anf (tag ast) in
    let vars = free_vars_P anfed [] in
    let c = Pervasives.compare in
    let str_list_print strs = "[" ^ (ExtString.String.join ", " strs) ^ "]" in
    assert_equal (List.sort c vars) (List.sort c expected) ~printer:str_list_print)
;;

let builtins_size = 4 * (List.length initial_env)

(* well-formedness tests *)
let wf_errs = [
  terr "duplicate_1" {| def f(x, x):
                          x
                      0  |}
      "" "The identifier x, redefined at <duplicate_1, 1:10-1:11>";
  
  terr "duplicate_2" {| let x = 1, x = 2 in x |} "" 
     "The identifier x, redefined at <duplicate_2, 1:12-1:13>";
  
  terr "duplicate_3" {| let x = (let y = 1, y = 2 in y) in x |} "" 
     "The identifier y, redefined at <duplicate_3, 1:21-1:22>";

  terr "fun_duplicate_1" {| def foo(x): 
                              x
                          def foo(y):
                              y
                          1  |} "" 
     "The function name foo, redefined at <fun_duplicate_1, 3:26-4:31>, duplicates one at <fun_duplicate_1, 1:1-2:31>";
  
  terr "unbound_1" {| x |} ""  
     "The identifier x, used at <unbound_1, 1:1-1:2>, is not in scope";
  
  terr "unbound_2" {| def f(x):
                        y
                    0 |} ""  
     "The identifier y, used at <unbound_2, 2:24-2:25>, is not in scope";
 
  terr "overflow_1" "1073741824" "" 
     "The number literal 1073741824, used at <overflow_1, 1:0-1:10>, is not supported in this language";

  terr "unbound_fun_1" {| f(1) |} 
     "" ""; (* caught by type synth *)
  
  terr "arity_mismatch_1" {| def f(x, y):
                                x + y
                            f(1) |} 
     "" ""; (* caught by type synth *)

  (* the following program should report 3 errors *)
  terr "errors_1" {| def f(x, x):
                       y
                   f(1) |} "" "";
];;

let runtime_errs = [
  (* integer overflow *)
  terr "runtime_overflow_1" "add1(1073741823)" "" "Error: Integer overflow";
  terr "runtime_overflow_2" "10737418 * 120" "" "Error: Integer overflow";

];;

let expr_tests = [
  (* arithmetic tests *)
  t "expr_1" "3" "" "3";
  t "expr_2" "1 + 2" "" "3";
  t "expr_3" "1 * 2 + 3" "" "5";
  t "times_1" "1073741823 * 1" "" "1073741823";
  t "add1_1" "add1(1)" "" "2";
  t "sub1_1" "sub1(1)" "" "0";
  t "isnum_1" "isnum(1)" "" "true";
  t "isnum_2" "isnum(true)" "" "false";
  
  (* logic tests *)
  t "isbool_1" "isbool(true)" "" "true";
  t "isbool_2" "isbool(false)" "" "true";
  t "isbool_3" "isbool(1)" "" "false";
  t "not_1" "!(true)" "" "false";
  t "not_2" "!(false)" "" "true";
  t "and_1" "true && true" "" "true";
  t "or_1" "true || true" "" "true";
  t "greater_1" "2 > 1" "" "true";
  t "greater_2" "2 > -1" "" "true";
  t "greater_3" "1 > 1" "" "false";

  t "greaterEq_1" "2 >= 1" "" "true";
  t "less_1" "1 < 2" "" "true";
  t "less_2" "1 < 0" "" "false";
  t "lessEq_1" "1 <= 2" "" "true"; 
  t "eq_1" "1 == 1" "" "true";
  t "eq_2" "1 == 0" "" "false";  
  t "eq_3" "false == false" "" "true";

  (* let tests *)
  t "let_1" "let x = 1 in x" "" "1";
  t "let_2" "let x = (1 == 2) in x" "" "false";
  t "let_3"  
  {| let x = true in
         let y = !(x) && x in
             y
  |} "" "false";
  t "let_4" 
  {| let x = 10 in
         let y = (if x >= (5 + 4): true else: false) in 
             isnum(x) && isnum(y)
  |} "" "false";

  (* let* semantics *)
  t "let_5" {| let x = 10, y = x * 2 in y |} "" "20";  

  (* if tests *)
  t "if_1" "if true: 1 else: 2" "" "1";
  t "if_2" "if false: 1 else: 2" "" "2";
  t "if_3" "if 3 > 2: 1 else: 2" "" "1";
  t "if_4" "if !(2 == (1 + 1)): 1 else: 2" "" "2";
  t "if_5" "if (let x = true in x): 1 else: 2" "" "1";
  t "if_6" "let x = 1 in if x > 0: 1 else: 2" "" "1";
];;

let renaming_tests = [
   t "rename_1" {| (let x = 1 in x) + (let x = 2 in x) |} "" "3";
(*   t "rename_2" {| def foo(x : Int) -> Int:
                       x + (let x = 1 in x) + (let x = 2 in x)
                    foo(3) |} "" "6";
*)
  ];;

let pair_tests = [
  t "tup1" "let t = (4, 1, (5, 6)) in
            begin
              t[0 of 2 := 7];
              t
            end" "" "(7, 1, (5, 6))";
  t "tup2" "type intlist = (Int * intlist)
            let t : intlist = (4, (5, nil : intlist)) in
            begin
              t[1 of 2 := nil : intlist];
              t
            end" "" "(4, nil)";
  t "tup3" "type intlist = (Int * intlist)
            let t : intlist = (4, (5, nil : intlist)) in
            begin
              t[1 of 2 := t];
              t
            end" "" "(4, <cyclic tuple 1>)";
  t "tup4" "let t = (4, 6) in
            (t, t)"
           ""
           "((4, 6), (4, 6))"

];;

let typed_fun_tests = [
  t "typed_fun_1" {|
    def typed_max(x: Int, y: Int) -> Int:
        if(x > y): x else: y

    typed_max(1, 2) * typed_max(2, 1)
  |} "" "4";

(*  t "typed_fun_2" {|
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
  |} "" "false\ntrue\ntrue\nfalse\nfalse";
*)
  t "typed_fun_3" {|
    def typed_q(x: Int) -> Int:
      let a = 1, b = -1, c = -2 in
        (a * x * x) + (b * x) + c

    (typed_q(0) == -2) && (typed_q(-1) == 0) && (typed_q(2) == 0)
  |} "" "true";
  
(*  t "typed_group_1" {|
        def foo() -> Int:
          1
        and
        def bar() -> Int:
          foo()

        bar(): Int
  |} "" "1";
*)
  terr "typed_group_err_1" {|
        def foo() -> Int:
          1
        and
        def bar() -> Int:
          foo()

        bar(): Bool
  |} "" "expected Bool but got Int";

];;

let fun_tests = [
  t "funx_1" {|
    def foo1(x):
      x + 6

    foo1(38)
  |} "" "44";
  
  t "funx_02" {|
    def foo2(x):
      let y = 6 in x + y

    foo2(38)
  |} "" "44";

  t "funx_03" {|
    def foo3(x):
      x == 1

    foo3(38)
  |} "" "false";

  t "fun_1" {|
    def max(x, y):
        if(x > y): x else: y

    max(1, 2) * max(2, 1)
  |} "" "4";

(*  t "fun_2" {|
    def nand(a, b):
      !(a && b)
    and
    def xor(a, b):
      nand(nand(a, nand(a, b)), nand(b, nand(a, b)))

    let a = print(xor(true, true)) in 
    let b = print(xor(true, false)) in
    let c = print(xor(false, true)) in
      print(xor(false, false))
  |} "" "false\ntrue\ntrue\nfalse\nfalse";
*)
  t "fun_3" {|
    def q(x):
      let a = 1, b = -1, c = -2 in
        (a * x * x) + (b * x) + c

    (q(0) == -2) && (q(-1) == 0) && (q(2) == 0)
  |} "" "true";

  t "fun_4" {|
    def mult(x, y):
      x * y
    and 
    def square(x):
      mult(x, x)
    square(3)
  |} "" "9";

  t "id_1" {|
    def id(x) : let y = x in x
    id(true)
  |} "" "true";

  t "fxyz" 
   {|
      let rec fxyz = (lambda(x, y, z):
        if(id(x)): id(y)
        else: id(z)) 
      , 
      id = (lambda(x): 
        x)
      in
      fxyz(true, 4, 5)
   |} "" "4";

  t "f_boolint" {| def f_boolint(x, y):
                (x == true) && (y == 1)

             f_boolint(true, 1) |} "" "true";

  t "recursive_1" {| 
      let rec factorial = (lambda(n):
        if (n == 0): 1 else: n * factorial(n - 1))
      in
      factorial(6) |} "" "720";

  t "recursive_2" {|
    let rec fib = (lambda(n):
      if(n == 1): 1 
        else: 
          if(n == 2): 1 
            else: fib(n - 1) + fib(n - 2))
    in
    fib(6) |} "" "8";

  t "mutual_1" {|
    let rec is_even = (lambda(n):
        if(n == 0): true
        else: is_odd(n - 1))
    ,
    is_odd = (lambda (n):
        if(n == 0): false
        else: is_even(n - 1))
    in
    is_even(20) && !(is_even(3)) && is_odd(5) 
  |} "" "true"; (* TODO *)

  (* this function call would stack-overflow without tail-call optimization *)
(*  t "tail_1" {|
      def tail1(x, y):
        if x > 0: tail1(x - 1, y + 1)
        else: y

      tail1(1000000, 0)  |} "" "1000000";
*)
  ];;

let arity_tests = [
t "arity_0" {| def f():
                 10
                 f() |} "" "10";
t "arity_1" {| def f(x, y, z):
                 (x * x) + (y * y) + (z * z)
             f(1, 2, 3)|} "" "14";
t "arity_2" {| def f(a, b, c, d):
                 (a * c) - (b * d) 
             f(1, 2, 3, 4)|} "" "-5";
t "arity_3" {| def f(a, b, c, d, e):
                 e
             f(1, 2, 3, 4, 5)|} "" "5";
t "arity_4" {| def f(a, b, c, d, e, f):
                 f
             f(1, 2, 3, 4, 5, 6)|} "" "6";
t "arity_5" {| def f(a, b, c, d, e, f, g):
                 g
             f(1, 2, 3, 4, 5, 6, 7)|} "" "7";
];;

let fun_tests = 
    typed_fun_tests
  @ fun_tests
  @ arity_tests
;;

let oom = [
  tgcerr "oomgc1" (6 + builtins_size) "(1, (3, 4))" "" "Out of memory";
  tgc "oomgc2" (8 + builtins_size) "(1, (3, 4))" "" "(1, (3, 4))";
  (*tvgc "oomgc3" (8 + builtins_size) "(1, (3, 4))" "" "(1, (3, 4))";*)
  tgc "oomgc4" (4 + builtins_size) "(3, 4)" "" "(3, 4)";
  tgcerr "oomgc5" (3 + builtins_size) "(3, 4, 5, 6, 7, 8, 9)" "" "Allocation";
];;

let gc = [
(*  tgc "gc_lam1" (10 + builtins_size)
      "let f = (lambda: (1, 2)) in
       begin
         f();
         f();
         f();
         f()
       end"
      ""
      "(1, 2)";
*)];;


let suite =
"suite">:::
   []
 @ wf_errs
 @ runtime_errs
 @ expr_tests 
 @ renaming_tests
 @ pair_tests 
 (*@ fun_tests*)
 @ oom 
 @ gc


let () =
  run_test_tt_main suite
;;

