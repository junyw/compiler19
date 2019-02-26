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

let t_typ name value expected = name>::
  (fun _ -> assert_equal expected value ~printer:string_of_typ);;


let unify_opt (t1 : 'a typ) (t2 : 'a typ) = 
  try 
    let _ = unify t1 t2 dummy_span [] in Ok(true)
  with 
    err -> Error(err)

(* test two types are equivalent up to unification *)
let t_typ_eq name value expected = name>::
  (fun _ -> assert_equal (Ok(true)) (unify_opt expected value) ~printer:dump);;

let forty_one = "41";;

let forty_one_a = (AProgram([], ACExpr(CImmExpr(ImmNum(41, ()))), ()))

let test_prog = "let x : Int = if sub1(55) < 54: (if 1 > 0: add1(2) else: add1(3)) else: (if 0 == 0: sub1(4) else: sub1(5)) in x"
let anf1 = (anf     (tag (parse_string "test" test_prog)))


let tX1 = mk_tyvar "X1" 
let tX2 = mk_tyvar "X2"
let tX3 = mk_tyvar "X3"

(* X1 -> X2 *)
let tX1toX2 = mk_tyarr [tX1] tX2
(* X1 X2 -> X3 *)
let tX1X2toX3 = mk_tyarr [tX1;tX2] tX3

let utility_tests = [
	(* type substitution tests *)
	t_any "apply_subst_typ_1" (apply_subst_typ [] (TyBlank(dummy_span)))  (TyBlank(dummy_span));
	t_any "apply_subst_typ_2" (apply_subst_typ [("X1", tInt)] tX1)  tInt;

	t_any "apply_subst_typ_3" 
		(apply_subst_typ [("X1", tInt)] tX1toX2) 
		(mk_tyarr [tInt] tX2);

	t_any "apply_subst_typ_4" 
		(apply_subst_typ [("X1", tX3); ("X2", tX3)] tX1toX2) 
		(mk_tyarr [tX3] tX3);

    (* unification tests *)
	t_any "unify_1"
		(unify tInt tInt dummy_span []) 
		[];

	t_any "unify_2"
		(unify tX1 tX1 dummy_span []) 
		[];

	t_any "unify_3"
		(unify tX1 tInt dummy_span []) 
		[("X1", tInt)];

	t_any "unify_4"
		(unify tInt tX1 dummy_span []) 
		[("X1", tInt)];

	t_any "unify_5"
		(unify (mk_tyarr [tInt; tInt] tInt) tX1X2toX3 dummy_span [])
		[("X1", tInt); ("X2", tInt); ("X3", tInt)];

	(* TODO: test unification failures *)
];;

(* helper function to create expr for testing *)
let mk_num n = ENumber(n, dummy_span)
let mk_bool (b : bool) = EBool(b, dummy_span)
let mk_var (x : string) : 'a expr = EId(x, dummy_span)
let mk_fun (name : string) (args : string list) scheme body  =
	DFun(name, List.map (fun x -> (x, dummy_span)) args, scheme, body, dummy_span)
;;
let mk_eprim1 (op : prim1) (x : 'a expr) = 
	EPrim1(op, x, dummy_span)
;;
let mk_eprim2 (op : prim2) (x : 'a expr) (y : 'a expr) = 
  EPrim2(op, x, y, dummy_span)
;;

let mk_typbind (name : string) (typ : 'a typ) = (name, typ, dummy_span);;
let mk_bind typbind expr = (typbind, expr, dummy_span);;
let mk_binding name typ expr = (mk_typbind name typ, expr, dummy_span);;

let mk_let (bindings : 'a bind list) (body : 'a expr) : 'a expr = 
	ELet(bindings, body, dummy_span)
;;

let mk_if (cond : 'a expr) (thn : 'a expr) (els : 'a expr) : 'a expr =
  EIf(cond, thn, els, dummy_span)
;;

let mk_app (f_name : string) (args : 'a expr list) =
  EApp(f_name, args, dummy_span)
;;

let mk_prog declgroups body =
  Program(declgroups, body, (TyBlank(dummy_span)), dummy_span)

let tyenv0 = StringMap.empty
let tyenv1 = StringMap.add "x" tInt tyenv0

let funenv0 = StringMap.empty
let funenv1 = StringMap.add "f" any2any funenv0

let get_2_3 (_, a, _) = a;;

(* type_expr : type an expression *)
let type_expr funenv env expr : 'a typ = 
  get_2_3 (infer_exp funenv env expr [])
;;
let type_decl funenv env decl : 'a typ = 
  get_2_3 (infer_decl funenv env decl [])
;;

let type_prog funenv p: 'a typ =
  let (ret_typ, _) = infer_prog funenv StringMap.empty p in
    ret_typ
;;
let inference_tests = [
	
	(* typing rules *)

	t_any "ty_num_1" 
		(infer_exp StringMap.empty tyenv0 (mk_num 3) []) 
		([], tInt, (mk_num 3));

	t_any "ty_var_1"
		(infer_exp StringMap.empty tyenv1 (mk_var "x") [])
		([], tInt, (mk_var "x"));

	t_typ "ty_let_1"
		(* let x = 1 in x *)
		(type_expr funenv0 tyenv0 
							(mk_let 
								[ (mk_binding "x" tX1 (mk_num 1)) ]
								(mk_var("x"))))
		tInt;

  t_typ "ty_if_1"
    (* if x == 1 then true else false *)
    (type_expr initial_env tyenv1
      (mk_if 
        (mk_eprim2 Eq (mk_var "x") (mk_num 1))
        (mk_bool true)
        (mk_bool false)))
    tBool;

  t_typ "ty_prim2_1" 
    (* 1 + x *)
    (type_expr initial_env tyenv1 
        (mk_eprim2 Plus (mk_var "x") (mk_num 1)))
    tInt;


  (* def f1(x): add1(x) *)
  (* should type f1 as Int -> Int *)
	t_typ "ty_abs_1"
		(get_2_3 (infer_decl initial_env tyenv0 (mk_fun "f1" ["x"] arrX2Y (mk_eprim1 Add1 (mk_var "x"))) []))
		(mk_tyarr [tInt] tInt);


  (* def f2(x): x + 6 *)
  (* should type f2 as Int -> Int *)
  t_typ "ty_abs_2"
    (get_2_3 (infer_decl initial_env tyenv0 (mk_fun "f2" ["x"] arrX2Y (mk_eprim2 Plus (mk_var "x") (mk_num 6))) []))
    (mk_tyarr [tInt] tInt);

  (* def f3(x, y): isnum(print(x)) && isbool(y) *)
  (* should type f3 as T1, T2 -> Bool *)
  t_typ_eq "ty_abs_3"
    (type_decl initial_env tyenv0 
      (mk_fun "f3" ["x"; "y"] arrXY2Z 
        (mk_eprim2 And
          (mk_eprim1 IsNum (mk_eprim1 Print (mk_var "x")))
          (mk_eprim1 IsBool (mk_var "y"))
      ))) 
    (mk_tyarr [tX1; tX2] tBool);
  
  (*
    def f(x):
      x + 6

    f(38)
  *)
  (* should type the final type of the program as Int *)
  t_typ "ty_prog_1"
    (type_prog initial_env
      (mk_prog
        [[(mk_fun "f3" ["x"] arrX2Y 
          (mk_eprim2 Plus
            (mk_var "x")
            (mk_num 6)))]] 
        (mk_app "f3" [(mk_num 38)])))
    tInt;

  (*
    def f(x, y):
      isnum(print(x)) && isbool(y)

    def g(z):
      f(z, 5)

    g(7)
  *)
  (* should type the final type as Bool *)
  t_typ "ty_prog_2"
    (type_prog initial_env
      (mk_prog
        (* declarations *)
        [[(mk_fun "f4" ["x"; "y"] arrXY2Z 
            (mk_eprim2 And
              (mk_eprim1 IsNum (mk_eprim1 Print (mk_var "x")))
              (mk_eprim1 IsBool (mk_var "y"))))];
          [(mk_fun "g1" ["z"] arrX2Y
            (mk_app "f4" [(mk_var "z"); (mk_num 5)]))]]
        (* body *)
        (mk_app "g1" [(mk_num 7)])))
    tBool;


  (* Typing mutually recursive functions *)
  (*
    def iseven(n):         
      if n == 0: true
      else: isodd(n - 1)
    def isodd(n): 
      if n == 0: false
      else: iseven(n - 1) 

    iseven(10)
  *)
  t_typ "ty_prog_3"
    (type_prog initial_env
      (mk_prog
        (* declarations *)
        [[(mk_fun "iseven" ["n"] arrX2Y
            (mk_if  (mk_eprim2 Eq (mk_var "n") (mk_num 0)) 
                    (mk_bool true) 
                    (mk_app "isodd" [(mk_eprim2 Minus (mk_var "n") (mk_num 1))])));
          (mk_fun "isodd" ["n"] arrX2Y
            (mk_if  (mk_eprim2 Eq (mk_var "n") (mk_num 0))  
                    (mk_bool false) 
                    (mk_app "iseven" [(mk_eprim2 Minus (mk_var "n") (mk_num 1))])));]]
        (* body *)
        (mk_app "iseven" [(mk_num 10)])))
    tBool;

];;


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
  (*t "lessEq_1" "1 <= 2" "true";*) (* TODO: should pass *)
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

  (* let* semantics *)
  t "let_5" {| let x = 10, y = x * 2 in y |} "20";  

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

let renaming_tests = [
   t "rename_1" {| (let x = 1 in x) + (let x = 2 in x) |} "3";
   t "rename_2" {| def foo(x):
                       x + (let x = 1 in x) + (let x = 2 in x)
                    foo(3) |} "6";
];;

let init_tests =
[
  t "expr_0" "3" "3";
  (* tanf "forty_one_anf"
       (Program([], ENumber(41, ()), TyBlank(), ()))
       forty_one_a; *)

  (* tanf "prim1_anf"
   *      (Program([], (EPrim1(Sub1, ENumber(55, ()), ())), ()))
   *      (AProgram([],
   *                (ALet("unary_1", CPrim1(Sub1, ImmNum(55, ()), ()),
   *                      ACExpr(CImmExpr(ImmId("unary_1", ()))),
   *                      ())),
   *               ())); *)

  (*te "scope_err1" "let x : Bool = true in (let y : Bool = (let x : Bool = false in x) in y)" "shadows one defined";*)

  (*ta "forty_one_run_anf" (atag forty_one_a) "41";*)
 
  (*t "forty_one" forty_one "41";*)


  (*t "test" test_prog "3";*)
      
    (* Some useful if tests to start you off *)

  (*t "if1" "if 7 < 8: 5 else: 3" "5";*)
  (*t "if2" "if 0 > 1: 4 else: 2" "2";*)

  (*te "overflow" "add1(1073741823)" "overflow";*)

  (*tvg "funcalls" "def fact(n : Int) -> Int: if n < 2: 1 else: n * fact(n - 1)\n\nfact(5)" "120"*)  
];;


let typing_tests = 
  utility_tests @
  inference_tests
;;
let language_tests = 
  expr_tests @
  renaming_tests 
  (*init_tests*)
;;
let all_tests = 
  typing_tests @
  language_tests  
;;

let suite =
"suite">::: all_tests
;;


let () =
  run_test_tt_main suite
;;
