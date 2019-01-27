open Compile
open Runner
open Printf
open OUnit2
open Pretty
open Types
       
let is_osx = Conf.make_bool "osx" false "Set this flag to run on osx";;

let t name program expected = name>::test_run program name expected;;

let ta name program expected = name>::test_run_anf program name expected;;

let te name program expected_err = name>::test_err program name expected_err;;

(* test A-Normal Form generation *)
let tanf name program expected = name>::fun _ ->
  assert_equal expected (anf (tag program)) ~printer:string_of_expr;;

(* helper function that converts generated ANF to string *)
let tanf' name program expected = name>::test_run_anf' program name expected;;

let teq name actual expected = name>::fun _ ->
  assert_equal expected actual ~printer:(fun s -> s);;

let tprog filename expected = filename>::test_run_input filename expected;;

let teprog filename expected = filename>::test_err_input filename expected;;

let forty_one = "41";;

let forty_one_a = (ENumber(41, ()))

(* testing generation of A-Normal Form *)
let anf_tests =  [
  
  tanf "forty_one_anf"
       (ENumber(41, ()))
       forty_one_a;

  (* tanf "prim1_anf"
       (EPrim1(Sub1, ENumber(55, ()), ()))
       (ELet(["$prim1_1", EPrim1(Sub1, ENumber(55, ()), ()), ()],
             EId("$prim1_1", ()),
             ()));
  
  tanf "prim2_anf"
       (EPrim2(Plus, ENumber(55, ()), ENumber(32, ()), ()))
       (ELet(["$prim2_1", EPrim2(Plus, ENumber(55, ()), ENumber(32, ()), ()), ()],
             EId("$prim2_1", ()),
             ())); *)  
  (*  ta "forty_one_run_anf" (tag forty_one_a) "41";*)
 
  (* tests that anf generates as few as let-bindings as possible *)  
   tanf' "anf_1" "1 + 2" "(1 + 2)"; 
   tanf' "anf_2" "let x = 1, y = 2 in x" "(let x = 1, y = 2 in x)";
   tanf' "anf_3" "let x = 1, y = 2 in x + y" "(let x = 1, y = 2 in (x + y))";
   tanf' "anf_4" "if 3 + 4: 1 else: 2" "(let $if_1 = (if (3 + 4): 1 else: 2) in $if_1)";
   tanf' "anf_5" "if 3 + 4: 1 + 2 else: 2" "(let $if_1 = (if (3 + 4): (1 + 2) else: 2) in $if_1)";
   tanf' "anf_6" "add1(1)" "add1(1)";
   tanf' "anf_7" "let x = 1 in add1(x)" "(let x = 1 in add1(x))";

];;

let arithmetic_tests = [
  (* tprog "test1.boa" "3"; *)
  t "int_1" "41" "41";
  t "int_2" "(41)" "41";
  t "unary_1" "sub1(3)" "2";
  t "unary_2" "add1(3)" "4";
  t "unary_3" "add1(sub1(add1(sub1(3))))" "3";
  t "arith_1" "1 + 2" "3";
  t "arith_2" "(1 + 2)" "3";
  t "arith_3" "1 - 2" "-1";
  t "arith_4" "1 + 2 - 3" "0";
  t "arith_5" "(1 + 2) - 3" "0";
  t "arith_6" "1 + (2 - 3)" "0";
  t "arith_7" "(1 + 2) - 3 - 4" "-4";
  t "arith_8" "1 * 2" "2";
  t "arith_9" "1 * 2 + 3" "5";
  t "arith_10" "1 * 2 + 3 - 4" "1";
  t "arith_11" "(1 + 2) * 3" "9";
  t "arith_12" "(1 + 2) * (2 - 4)" "-6";
  t "arith_13" "(1 + (2 * 3) - 4) * (2 - 4)" "-6";
  t "arith_14" "sub1(1 * 2 + 3)" "4";
  t "arith_15" "sub1(1 * add1(2) + 3)" "5";
  t "arith_16" "3 + 2 * 3" "9";
  t "arith_17" "3 + sub1(3) * add1(2)" "9";
  t "arith_18" "(add1(1) + add1(2)) - add1(3)" "1";

  (* More tests here *)
];;

let let_tests = [
  t "let_1" "let x = 1 in x" "1";
  t "let_2" "let x = 2, y = 3 in y" "3";
  t "let_3" {| let x = 2 in 
                 let y = x in y |}
  "2";
  t "let_4" {| let x = 2 in 
                 let y = 3 in x |}
  "2";
  t "let_5" {| let x = 2, y = 3 in 
                 let z = 4 in x |}
  "2";
  t "let_6" {| let x = 2 in x + 3 |}
  "5";
  t "let_7" {| let x = 2, y = 3 in 
                   x * y + x |}
  "8";
  t "let_8" {| let x = 2, y = 3 in 
                   let z = 4 in
                       (x + z) * (y - z) |}
  "-6";
  t "let_9" {| let x = 2, y = 3 in 
                       sub1(x) * add1(y) |}
  "4";
  t "let_10" {| let x = 2 in 
                  let y = 3 in 
                      sub1(x) * add1(y) |}
  "4";
  t "let_11" {| let x = 2 in 
                  let y = 3 in 
                      x + sub1(x) * add1(y) |}
  "6";
  t "let_12" {| let x = 2 * (3 + 2) in 
                  let y = sub1(x) in 
                      x + 3 * y |}
  "37";
  t "let_13" {| let x = 2 * (3 + 2) in 
                  let y = sub1(x) * 2 in 
                      x + 3 * y |}
  "64";
];;
let if_tests = [
  t "if_1" "if 5: 4 else: 2" "4";  
  t "if_2" "if 0: 4 else: 2" "2"; 
  t "if_3" "if (1 - 1): 4 else: 2" "2";
  t "if_4" "if (1 - 1): 4 else: 2 * (3 - 2)" "2";
  t "if_5" {| let x = 2, y = 2 in
                  if y - x: 4 else: 2 |} "2";
  t "if_6" {| let x = 2, y = 2 in
                  if y - x: 4 
                  else: y * x |} "4";
  t "if_7" {| let x = if 1: 2 else: 3 in
                  x |} "2";
  t "if_8" {| let x = 1, y = 3 in
                  if x: y else: x |} "3";
  t "if_9" {| let x = 1, y = if x: x else: 2 in
                  y |} "1";
  t "if_10" {| let x = 0, y = if x: x else: 2 in
                  y |} "2";
  t "if_11" {| let x = 2 * 2 + 1, y = x * 2, z = y - (x * y) in z |} "-40";
  t "if_12" {| let x = add1(4), y = x * add1(1), z = y - (x * y) in z |} "-40";
  t "if_13" {| let c1 = 1 in
                let c2 = 2 in
                  let x = (if c1: 5 + 5 else: 6 * 2) in
                    let y = (if c2: x * 3 else: x + 5) in
                      x + y |} "40";
  (* let within if *)
  t "if_14" {| if (let x = 0 in x + 1): 1 else: 2 |} "1"; 
];;

let binding_errors = [
  te "unbound_1" "let x = 1 in y" "Unbound variable y";
  te "unbound_2" "let x = 1, y = z in x" "Unbound variable z";
  te "redefined_1" "let x = 1, x = 2 in x" "Variable x is redefined";
  te "redefined_2" "let x = 1 in let x = 2 in x" "Variable x is redefined";
];;

let all_tests = 
  anf_tests @
  arithmetic_tests @
  let_tests @
  if_tests @
  binding_errors
;;

let suite =
"suite">::: all_tests
;;


let () =
  run_test_tt_main suite
;;
