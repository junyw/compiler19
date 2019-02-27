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

(* t_typ: test if two types are equal *)
let t_typ name value expected = name>::
  (fun _ -> assert_equal expected value ~printer:string_of_typ);;

(* t_typ_eq: test two types are equal up to unification *)
let t_typ_eq name value expected = name>::
  (fun _ -> 
    try 
      let subst = unify value expected dummy_span [] in
      let t1 = apply_subst_typ subst value in
      let t2 = apply_subst_typ subst expected in
        assert_equal t1 t2 ~printer:dump
    with 
      err -> assert_equal value expected ~printer:string_of_typ)
;;

(* well-formedness tests *)
let wf_tests = [
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
  
  (* TODO *)
  (*te "shadow_1" "let x : Bool = true in (let y : Bool = (let x : Bool = false in x) in y)" "shadows one defined";*)

];;


(* type variables for testing *)
let tX1 = mk_tyvar "X1" 
let tX2 = mk_tyvar "X2"
let tX3 = mk_tyvar "X3"

(* X1 -> X2 *)
let tX1toX2 = mk_tyarr [tX1] tX2
(* X1 X2 -> X3 *)
let tX1X2toX3 = mk_tyarr [tX1;tX2] tX3

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

(* type_expr : type an function declaration *)
let type_decl funenv env decl : 'a typ = 
  get_2_3 (infer_decl funenv env decl [])
;;

(* type_prog : type an program and return the return type of the program *)
let type_prog funenv p: 'a typ =
  let (ret_typ, _) = infer_prog funenv StringMap.empty p in
    ret_typ
;;

(* test utility functions for type inference *)
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
    [("X3", tInt); ("X1", tInt); ("X2", tInt)];

  (* unify X1 -> Int and X2 -> X2 *)
  (* [X1 => Int, X2 => Int] *)
  t_any "unify_6"
    (unify (mk_tyarr [tX1] tInt) (mk_tyarr [tX2] tX2)  dummy_span [])
    [("X2", tInt); ("X1", tInt)];
  
  (* unify Int -> X1 and X2 -> X2 *)
  t_any "unify_7"
    (unify (mk_tyarr [tInt] tX1) (mk_tyarr [tX2] tX2)  dummy_span [])
    [("X1", tInt); ("X2", tInt)];

  (* unify X2 -> X2 and Int -> X1*)
  t_any "unify_8"
    (unify (mk_tyarr [tX2] tX2) (mk_tyarr [tInt] tX1)  dummy_span [])
    [("X1", tInt); ("X2", tInt)];

  (* generalization *)
  t_any "generalize_1"
    (generalize StringMap.empty (mk_tyarr [tX1] tX2))
    (SForall(["X2";"X1"], (mk_tyarr [tX1] tX2), dummy_span));

  t_any "generalize_2"
    (generalize StringMap.empty (mk_tyarr [tBool] tBool))
    (SForall([], (mk_tyarr [tBool] tBool), dummy_span));

];;


let inference_tests = [

	t_any "ty_num_1" 
		(infer_exp StringMap.empty tyenv0 (mk_num 3) []) 
		([], tInt, (mk_num 3));

	t_any "ty_var_1"
		(infer_exp StringMap.empty tyenv1 (mk_var "x") [])
		([], tInt, (mk_var "x"));

	t_typ "ty_let_1"
		(* let x = 1 in x *)
    (* should have type Int *)
		(type_expr funenv0 tyenv0 
							(mk_let 
								[ (mk_binding "x" tX1 (mk_num 1)) ]
								(mk_var("x"))))
		tInt;

  t_typ "ty_if_1"
    (* if x == 1 then true else false *)
    (* should have type Bool *)
    (type_expr initial_env tyenv1
      (mk_if 
        (mk_eprim2 Eq (mk_var "x") (mk_num 1))
        (mk_bool true)
        (mk_bool false)))
    tBool;

  t_typ "ty_prim2_1" 
    (* 1 + x *)
    (* should have type Int *)
    (type_expr initial_env tyenv1 
        (mk_eprim2 Plus (mk_var "x") (mk_num 1)))
    tInt;

	t_typ "ty_abs_1"
    (* def f1(x): add1(x) *)
    (* should type f1 as Int -> Int *)
		(type_decl initial_env tyenv0 
      (mk_fun "f1" ["x"] arrX2Y (mk_eprim1 Add1 (mk_var "x"))))
		(mk_tyarr [tInt] tInt);


  t_typ "ty_abs_2"
    (* def f2(x): x + 6 *)
    (* should type f2 as Int -> Int *)
    (type_decl initial_env tyenv0 
      (mk_fun "f2" ["x"] arrX2Y (mk_eprim2 Plus (mk_var "x") (mk_num 6))))
    (mk_tyarr [tInt] tInt);

  t_typ_eq "ty_abs_3"
    (* def fxy(x, y): isnum(print(x)) && isbool(y) *)
    (* should type fxy as T1, T2 -> Bool *)
    (type_decl initial_env tyenv0 
      (mk_fun "fxy" ["x"; "y"] arrXY2Z 
        (mk_eprim2 And
          (mk_eprim1 IsNum (mk_eprim1 Print (mk_var "x")))
          (mk_eprim1 IsBool (mk_var "y"))
      ))) 
    (mk_tyarr [tX1; tX2] tBool);
  
  t_typ "polymorphic_1"
    (* def f4(x): x == 1 *)
    (* should type f4 as Int -> Bool *)
    (type_decl initial_env tyenv0
      (mk_fun "f4" ["x"] arrX2Y
        (mk_eprim2 Eq (mk_var "x") (mk_num 1))))
    (mk_tyarr [tInt] tBool);

  t_typ "polymorphic_2"
    (* def f5(x): if x == 1: 10 else: 11 *)
    (* should type f4 as Int -> Int *)
    (type_decl initial_env tyenv0
      (mk_fun "f5" ["x"] arrX2Y
        (mk_if
          (mk_eprim2 Eq (mk_var "x") (mk_num 1))
          (mk_num 10)
          (mk_num 11))))
    (mk_tyarr [tInt] tInt);

  t_typ_eq "polymorphic_3"  
    (* def f6(x): isNum(x) *)
    (* should type f6 as T1 -> Bool *)
    (type_decl initial_env tyenv0
      (mk_fun "f6" ["x"] arrX2Y
        (mk_eprim1 IsNum (mk_var "x"))))
    (mk_tyarr [tX1] tBool);

  t_typ_eq "polymorphic_4"
    (* def whatever1(x): x *)
    (* should type whatever1 as T1 -> T2 *)
    (type_decl initial_env tyenv0
      (mk_fun "whatever" ["x"] arrX2Y
        (mk_var "x")))
    (mk_tyarr [tX1] tX2);

  t_typ_eq "polymorphic_5"
    (* def whatever2(x, y): x *)
    (* should type whatever2 as T1 T2 -> T3 *)
    (type_decl initial_env tyenv0
      (mk_fun "whatever2" ["x"; "y"] arrXY2Z
        (mk_var "x")))
  (mk_tyarr [tX1; tX2] tX3);


  t_typ_eq "polymorphic_6"
    (* def identity(x): let y = x in y *)
    (* should type identity as T1 -> T1 *)

    (type_decl initial_env tyenv0
      (mk_fun "identity" ["x"] arrX2Y
        (mk_let [(mk_binding "y" tX3 (mk_var "x"))] (mk_var "y"))))
    (mk_tyarr [tX1] tX1);

  t_typ "type_if_expr_1"
    (* def f8(x): if x: false else: true *)
    (* should type f8 as Bool -> Bool *)
    (type_decl initial_env tyenv0
      (mk_fun "f8" ["x"] arrX2Y
        (mk_if (mk_var "x")
               (mk_bool false)
               (mk_bool true))))
    (mk_tyarr [tBool] tBool);

  t_typ "ty_prog_1"
  (* def f(x):
      x + 6
     f(38) *)
  (* should type the final type of the program as Int *)
  (type_prog initial_env
    (mk_prog
      [[(mk_fun "f3" ["x"] arrX2Y 
        (mk_eprim2 Plus
          (mk_var "x")
          (mk_num 6)))]] 
      (mk_app "f3" [(mk_num 38)])))
  tInt;

  t_typ "ty_prog_2"
  (* def f(x, y):
       isnum(print(x)) && isbool(y)
     def g(z):
       f(z, 5)
     g(7) 
  *)
  (* should type the final type as Bool *)
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

let type_error = [

  te "ty_add1_error" "add1(true)" 
     "Type error at ty_add1_error, 1:0-1:10: expected Int but got Bool";
  
  te "ty_not_error_1" "!(3)" 
     "Type error at ty_not_error_1, 1:0-1:4: expected Bool but got Int";
  
  te "ty_logic_error_1" "1 && true" 
     "Type error at ty_logic_error_1, 1:0-1:9: expected Bool but got Int";
  
  te "ty_logic_error_2" "false && 1" 
     "Type error at ty_logic_error_2, 1:0-1:10: expected Bool but got Int";
  
  te "ty_compare_error_1" "true > 1" 
     "Type error at ty_compare_error_1, 1:0-1:8: expected Int but got Bool";
  
  te "ty_if_error_1" "if 54: true else: false" 
     "Type error at ty_if_error_1, 1:0-1:23: expected Bool but got Int";
  
  te "ty_if_error_2" "let x = 1 in (if x: true else: false)" 
     "Type error at ty_if_error_2, 1:14-1:36: expected Bool but got Int";
  
  te "ty_if_error_3" "if (let x = 1 in x): true else: false" 
    "Type error at ty_if_error_3, 1:0-1:37: expected Bool but got Int";

  te "ty_mismatch_1" {| def foo(b, a):
                            if b: (a + 0) < 1
                            else: a && true
                        foo(1, 2)
                     |}
      "Type error at ty_mismatch_1, 3:34-3:43: expected Bool but got Int";
];;


let expr_tests = [
  (* arithmetic tests *)
  t "expr_1" "3" "3";
  t "expr_2" "1 + 2" "3";
  t "expr_3" "1 * 2 + 3" "5";
  t "times_1" "1073741823 * 1" "1073741823";
  te "runtime_overflow_1" "add1(1073741823)" "Error: Integer overflow";
  te "runtime_overflow_2" "10737418 * 120" "Error: Integer overflow";
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
  t "greaterEq_1" "2 >= 1" "true";
  t "less_1" "1 < 2" "true";
  t "less_2" "1 < 0" "false";
  t "lessEq_1" "1 <= 2" "true"; 
  t "eq_1" "1 == 1" "true";
  t "eq_2" "1 == 0" "false";  
  
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

  t "fxy" {| def fxy(x, y):
                (y == 1)

             fxy(true, 1) |} "true";

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
  t "tail_1" {|
      def tail1(x, y):
        if x > 0: tail1(x - 1, y + 1)
        else: y

      tail1(1000000, 0)  |} "1000000";
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

let wellformedness_tests = 
  wf_tests
;;

let typing_tests = 
    utility_tests 
  @ inference_tests 
  @ type_expr_tests
  @ type_error
;;
let language_tests = 
    expr_tests 
  @ renaming_tests
  @ typed_fun_tests
  @ fun_tests
  @ arity_tests
;;
let all_tests = 
    wellformedness_tests
  @ typing_tests
  @ language_tests  
;;

let suite =
"suite">::: all_tests
;;


let () =
  run_test_tt_main suite
;;
