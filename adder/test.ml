open Compile
open Runner
open Printf
open OUnit2

let t (name : string) (program : string) (expected : string) : OUnit2.test =
  name>::test_run program name expected;;
let te (name : string) (program : string) (expected_err : string) : OUnit2.test =
  name>::test_err program name expected_err;;

let int_tests = [
  t "forty_one" "41" "41";
  t "add1_5" "(add1 5)" "6";
  t "sub1_5" "(sub1 5)" "4";
  t "add1_neg5" "(add1 -5)" "-4";
  t "sub1_neg5" "(sub1 -5)" "-6";
  t "sub1_sub1" "(sub1 (sub1 5))" "3";
  t "add1_sub1" "(add1 (sub1 5))" "5";
  t "sub1_add1_sub1" "(sub1 (add1 (sub1 5)))" "4";
  (* More tests here *)
];;

let let_tests = [
  t "let_1" "(let ((x 5)) x)" "5";
  t "let_2" "(let ((x 5)) (add1 x))" "6";
  t "let_3" "(let ((x 5) (y x)) y)" "5";
  t "let_4" "(let ((x 5) (y 6)) y)" "6";
  t "let_5" "(let ((x 5) (y (sub1 x))) (sub1 y))" "3";
  t "let_6" "(let ((x 5) (y (sub1 x)) (z (sub1 y))) (sub1 z))" "2";
  t "let_7" "(let ((x 5) (x 6)) x)" "6";
  t "let_8" "(let ((x 5) (x 6) (y x)) y)" "6";
  t "let_9" "(let ((x (let ((x 5)) (sub1 x)))) x)" "4";
  (* More tests here *)
];;

let more_tests = [
  t "more_1" 
  {| (let ((x 1) (y (add1 x)))
  	      (let ((z (sub1 y)))
               (add1 (sub1 y)))) 
  |} "2";
  t "more_2"
  {| (let ((x 1) (y (let ((x 10)) (sub1 (sub1 x)))))
  	      (let ((x y) (z x))
  	           (sub1 z))) 
  |} "7";
  t "more_3"
  {| (let ((x 1) (x 2) (x 0)) 
  	      x)
  |} "0";
  t "more_4"
  {| (let ((x 1))
  	      (let ((x 2))
  	      	   (let ((x 3)) x)))
  |} "3";
  t "more_5"
  {| (let ((x 1))
  	      (let ((y 2)) x)) 
  |} "1";
  t "more_6"
  {| (let ((a 1))
  	      (let ((x 2) (a (add1 x)))
  	           (let ((x 3)) a)))
  |} "3";
  t  "more_7" "(let ((let 10)) let)" "10"; (* ? *)
  t  "more_8" "(let ((sub1 10)) (sub1 sub1))" "9"; (* ? *)
];;

let fail_tests = [
  te "fail_1" "(x 10)" "Undefined identifier x at line 0, col 1--line 0, col 2";
  te "fail_2" "(let ((x 10)) foo)" "Unbound variable foo at line 0, col 14--line 0, col 17";
  te "fail_3" "(x 10)" "Undefined identifier x at line 0, col 1--line 0, col 2";
  te "fail_4" "(let () 10)" "Expecting a list of bindings at line 0, col 5--line 0, col 7 but got nothing";
  te "fail_5" "(let (x 10) 10)" "Expecting a list at line 0, col 6--line 0, col 7"
];;

let all_tests = 
	int_tests @
	let_tests @
	more_tests @
  fail_tests
;;

let suite : OUnit2.test =
"suite">:::all_tests
;;


let () =
  run_test_tt_main suite
;;
