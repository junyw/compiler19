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

(* test the tag and anf function *)
let tanf name program expected = name>::fun _ ->
  assert_equal expected (anf (tag program)) ~printer:string_of_expr;;

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

  tanf "prim1_anf"
       (EPrim1(Sub1, ENumber(55, ()), ()))
       (ELet(["$prim1_1", EPrim1(Sub1, ENumber(55, ()), ()), ()],
             EId("$prim1_1", ()),
             ()));
  
  tanf "prim2_anf"
       (EPrim2(Plus, ENumber(55, ()), ENumber(32, ()), ()))
       (ELet(["$prim2_1", EPrim2(Plus, ENumber(55, ()), ENumber(32, ()), ()), ()],
             EId("$prim2_1", ()),
             ()));

  ta "forty_one_run_anf" (tag forty_one_a) "41";
 
  (*  tprog "test1.boa" "3";*)      
];;

let arithmetic_tests = [
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

];;

let all_tests = 
  anf_tests @
  arithmetic_tests @
  let_tests @
  if_tests
;;

let suite =
"suite">::: all_tests
;;


let () =
  run_test_tt_main suite
;;
