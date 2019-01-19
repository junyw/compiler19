open Sexp
open OUnit2
open Expr
open ExtLib

(* a helper for testing integers *)
let t_int name value expected = name>::
  (fun _ -> assert_equal expected value ~printer:string_of_int);;

(* A helper for testing primitive values (won't print datatypes well) *)
let t_any name value expected = name>::
  (fun _ -> assert_equal expected value ~printer:dump);;

let t_failure name f error = name>::
  (fun _ -> assert_raises error f);;

(* Feel free to add any new testing functions you may need *)


(* It can be useful to aggregate tests into lists if they test separate
functions, and put them together at the end *)

let env1 = [("a", 5); ("b", 15)];;
  
let get_tests = [
  t_any "get0" (get [] "a")   None;
  t_any "get1" (get env1 "a") (Some 5);
  t_any "get2" (get env1 "b") (Some 15);
  t_any "get3" (get env1 "c") None;
  (* More tests here *)
];;

let contains_tests = [
  t_any "contains0" (contains [] "a") false;
  t_any "contains1" (contains env1 "c") false;
  t_any "contains2" (contains env1 "a") true;
  (* More tests here *)
];;

let add_tests = [
  t_any "add0" (contains (add [] "c" 20) "c") true;
  t_any "add1" (contains (add env1 "c" 20) "c") true;
  t_any "add2" (contains (add env1 "c" 20) "d") false;
  t_any "add3" (get (add env1 "c" 20) "c") (Some 20);
  (* More tests here *)
];;

let evaluate_tests = [
  t_int "evaluate1" (evaluate (Times(Num 0, Num 5)) []) 0;
  t_int "evaluate2" (evaluate (Times(Num 1, Num 5)) []) 5;
  t_int "evaluate3" (evaluate (Times(Plus(Variable "x", Variable "y"), Num 5))
                      [("x", 5); ("y", 7)]) 60;
  t_int "evaluate4" (evaluate (Times(Plus(Times(Variable "a", Variable "b"), Times(Num 7, Variable "c")), Variable "d")) 
                    (add (add (add (add [] "a" 4) "b" 5) "c" 6) "d" 1))
                    62;

  t_failure "evaluate_error1" (fun () -> (evaluate (Times(Variable "x", Num 5)) [])) 
                              (Failure "Error: variable x is not in scope.");

  (* More tests here *)
];;

let pretty_tests = [
  t_any "pretty1" (pretty (Plus(Plus(Times(Plus(Num 5, Variable "y"), Variable "x"), Num 2), Num 1))) 
                  "(5 + y)x + 2 + 1";
  t_any "pretty2" (pretty (Plus(Plus(Num 1, Times(Num 2, Num 3)), Num 4))) 
                  "1 + 2 * 3 + 4";
  t_any "pretty3" (pretty (Plus(Times(Plus(Num 1, Num 2), Num 3), Num 4))) 
                  "(1 + 2) * 3 + 4";
  t_any "pretty4" (pretty (Plus(Times(Variable "a", Variable "b"), Num 4))) 
                  "ab + 4";
  t_any "pretty5" (pretty (Times(Plus(Times(Variable "a", Variable "b"), Times(Num 7, Variable "c")), Variable "d"))) 
                  "(ab + 7c)d";
  t_any "pretty5" (pretty (Times(Plus(Times(Variable "a", Variable "b"), Times(Num 7, Variable "c")), (Plus(Variable "d", Variable "e"))))) 
                  "(ab + 7c)(d + e)";
  t_any "pretty6" (pretty (Times(Times(Num 2, Num 3), Variable "x"))) 
                  "2 * 3x";
  t_any "pretty7" (pretty (Times(Num 2, Times(Num 3, Variable "x"))))
                  "2 * 3x";
  t_any "pretty7" (pretty (Times(Num 2, Times(Num 3, Plus(Variable "x", Num 0)))))
                  "2 * 3(x + 0)";

  (* More tests here *)
];;

let all_arith_tests =
  get_tests @
  contains_tests @
  add_tests @
  evaluate_tests @
  pretty_tests
  (* More tests here *)
;;

let arith_suite = "arithmetic_evaluation">:::all_arith_tests
;;

run_test_tt_main arith_suite
;;

let all_sexp_tests = [
    t_any "parse1" (parse"()")
                       (Ok [Nest ([], (0, 0, 0, 2))]);
    t_any "parse2" (parse"(a b)")
                       (Ok [Nest ([Sym("a", (0, 1, 0, 2)); Sym("b", (0, 3, 0, 4))], (0, 0, 0, 5))]);
    t_any "parse3" (parse "(a (b true) 3)")
                       (Ok [Nest ([Sym ("a", (0, 1, 0, 2));
                                  Nest([Sym  ("b", (0, 4, 0, 5));
                                        Bool (true, (0, 6, 0, 10))],
                                      (0, 3, 0, 11));
                                  Int (3, (0, 12, 0, 13))],
                            (0, 0, 0, 14))]);
    t_any "parse4" (parse"(a b c)")
                       (Ok [Nest ([Sym("a", (0, 1, 0, 2)); Sym("b", (0, 3, 0, 4)); Sym("c", (0, 5, 0, 6))], (0, 0, 0, 7))]);
    t_any "parse5" (parse"(a 1)")
                       (Ok [Nest ([Sym("a", (0, 1, 0, 2)); Int(1, (0, 3, 0, 4))], (0, 0, 0, 5))]);

    t_any "parse_error1" (parse ")")        (Error "Unmatched right paren at line 0, col 0");
    t_any "parse_error2" (parse "(")        (Error "Unmatched left paren at line 0, col 0");
    t_any "parse_error3" (parse "(a")       (Error "Unmatched left paren at line 0, col 0");
    t_any "parse_error4" (parse "(a (b c")  (Error "Unmatched left paren at line 0, col 3");
    t_any "parse_error5" (parse "(a))")     (Error "Unmatched right paren at line 0, col 3");
    t_any "parse_error6" (parse "(a ((b c") (Error "Unmatched left paren at line 0, col 4");

    (* More tests here *)
  ]
;;

let sexp_suite = "sexp_parsing">:::all_sexp_tests
;;

run_test_tt_main sexp_suite
;;

