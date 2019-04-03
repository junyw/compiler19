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

let oom = [
  tgcerr "oomgc1" (7 + builtins_size) "(1, (3, 4))" "" "Out of memory";
(*  tgc "oomgc2" (8 + builtins_size) "(1, (3, 4))" "" "(1, (3, 4))";
  tvgc "oomgc3" (8 + builtins_size) "(1, (3, 4))" "" "(1, (3, 4))";
  tgc "oomgc4" (4 + builtins_size) "(3, 4)" "" "(3, 4)";
  tgcerr "oomgc5" (3 + builtins_size) "(3, 4, 5, 6, 7, 8, 9)" "" "Allocation";
*)];;

let gc = [
  tgc "gc_lam1" (10 + builtins_size)
      "let f = (lambda: (1, 2)) in
       begin
         f();
         f();
         f();
         f()
       end"
      ""
      "(1, 2)";
];;


let suite =
"suite">:::
   []
 (*expr_tests *)
 @ pair_tests 
 (*@ oom *)
 (*@ gc*)


let () =
  run_test_tt_main suite
;;

