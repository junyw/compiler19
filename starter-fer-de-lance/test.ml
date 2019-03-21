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


let forty_one = "41";;

let forty_one_a = (AProgram([], ACExpr(CImmExpr(ImmNum(41, ()))), ()))

let test_prog = "let x : Int = if sub1(55) < 54: (if 1 > 0: add1(2) else: add1(3)) else: (if 0 == 0: sub1(4) else: sub1(5)) in x"
let anf1 = (anf     (tag (parse_string "test" test_prog)))

let suite =
"suite">:::
 [

  tanf "forty_one_anf"
    (Program([], [], EAnnot(ENumber(41, ()), TyBlank(), ()), ()))
    ""
    forty_one_a;

  (* tanf "prim1_anf"
   *      (Program([], (EPrim1(Sub1, ENumber(55, ()), ())), ()))
   *      (AProgram([],
   *                (ALet("unary_1", CPrim1(Sub1, ImmNum(55, ()), ()),
   *                      ACExpr(CImmExpr(ImmId("unary_1", ()))),
   *                      ())),
   *               ())); *)

  terr "scope_err1" "let x : Bool = true in (let y : Bool = (let x : Bool = false in x) in y)" "" "shadows one defined";

  ta "forty_one_run_anf" (atag forty_one_a) "" "41";
 
  t "forty_one" forty_one "" "41";


  t "test" test_prog "" "3";
      
    (* Some useful if tests to start you off *)

  t "if1" "if 7 < 8: 5 else: 3" "" "5";
  t "if2" "if 0 > 1: 4 else: 2" "" "2";

  terr "overflow" "add1(1073741823)" "" "overflow";

  tvg "funcalls" "def fact(n : Int) -> Int: if n < 2: 1 else: n * fact(n - 1)\n\nfact(5)" "" "120"
  
  ]
;;


let () =
  run_test_tt_main suite
;;
