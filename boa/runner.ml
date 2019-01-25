open Unix
open Filename
open Str
open Compile
open Printf
open OUnit2
open ExtLib
open Lexing

type ('a, 'b) either =
  | Left of 'a
  | Right of 'b

let either_printer e =
  match e with
    | Left(v) -> sprintf "Error: %s\n" v
    | Right(v) -> v

let string_of_position p =
  sprintf "%s:line %d, col %d" p.pos_fname p.pos_lnum (p.pos_cnum - p.pos_bol);;

let parse name lexbuf =
  try 
    lexbuf.lex_curr_p <- { lexbuf.lex_curr_p with pos_fname = name };
    Parser.program Lexer.token lexbuf
  with
  | (Failure msg) as exn ->
     if msg = "lexing: empty token" then
       failwith (sprintf "lexical error at %s" (string_of_position lexbuf.lex_curr_p))
     else
       let bt = Printexc.get_raw_backtrace () in
       Printexc.raise_with_backtrace exn bt (* make sure we throw with the same stack trace *)

let parse_string name s = 
  let lexbuf = Lexing.from_string s in
  parse name lexbuf

let parse_file name input_file = 
  let lexbuf = Lexing.from_channel input_file in
  parse name lexbuf

let compile_file_to_string name input_file =
  let input_program = parse_file name input_file in
  (compile_to_string input_program);;

let compile_string_to_string name s =
  let input_program = parse_string name s in
  (compile_to_string input_program);;

let make_tmpfiles name =
  let (null_stdin, _) = pipe() in
  let stdout_name = (temp_file ("stdout_" ^ name) ".out") in
  let stdin_name = (temp_file ("stderr_" ^ name) ".err") in
  (openfile stdout_name [O_RDWR] 0o600, stdout_name,
   openfile stdin_name [O_RDWR] 0o600, stdin_name,
   null_stdin)

(* Read a file into a string *)
let string_of_file file_name =
  let inchan = open_in file_name in
  really_input_string inchan (in_channel_length inchan)

let run_asm asm_string out =
  let outfile = open_out (out ^ ".s") in
  fprintf outfile "%s" asm_string;
  close_out outfile;
  let (bstdout, bstdout_name, bstderr, bstderr_name, bstdin) = make_tmpfiles "build" in
  let (rstdout, rstdout_name, rstderr, rstderr_name, rstdin) = make_tmpfiles "build" in
  let built_pid = Unix.create_process "make" (Array.of_list [""; out ^ ".run"]) bstdin bstdout bstderr in
  let (_, status) = waitpid [] built_pid in

  let try_running = match status with
  | WEXITED 0 ->
    Right(string_of_file rstdout_name)
  | WEXITED n ->
    Left(sprintf "Finished with error while building %s:\n%s" out (string_of_file bstderr_name))
  | WSIGNALED n ->
    Left(sprintf "Signalled with %d while building %s." n out)
  | WSTOPPED n ->
    Left(sprintf "Stopped with signal %d while building %s." n out) in

  let result = match try_running with
  | Left(_) -> try_running
  | Right(msg) ->
    printf "%s" msg;
    let ran_pid = Unix.create_process ("./" ^ out ^ ".run") (Array.of_list []) rstdin rstdout rstderr in
    let (_, status) = waitpid [] ran_pid in
    match status with
      | WEXITED 0 -> Right(string_of_file rstdout_name)
      | WEXITED n -> Left(sprintf "Error %d: %s" n (string_of_file rstdout_name))
      | WSIGNALED n ->
        Left(sprintf "Signalled with %d while running %s." n out)
      | WSTOPPED n ->
        Left(sprintf "Stopped with signal %d while running %s." n out) in

  List.iter close [bstdout; bstderr; bstdin; rstdout; rstderr; rstdin];
  List.iter unlink [bstdout_name; bstderr_name; rstdout_name; rstderr_name];
  result

let run p out =
  let maybe_asm_string =
    try Right(compile_to_string p)
    with
    | BindingError s -> Left("Binding error: " ^ s)
    | Failure s -> Left("Compile error: " ^ s)
    | err -> Left("Unexpected compile error: " ^ Printexc.to_string err)
  in    
  match maybe_asm_string with
  | Left(s) -> Left(s)
  | Right(asm_string) ->
    run_asm asm_string out

let run_anf p out =
  let maybe_asm_string =
    try Right(compile_anf_to_string p)
    with
    | BindingError s -> Left("Binding error: " ^ s)
    | Failure s -> Left("Compile error: " ^ s)
    | err -> Left("Unexpected compile error: " ^ Printexc.to_string err)
  in    
  match maybe_asm_string with
  | Left(s) -> Left(s)
  | Right(asm_string) ->
    run_asm asm_string out


let test_run program_str outfile expected test_ctxt =
  let full_outfile = "output/" ^ outfile in
  let program = parse_string outfile program_str in
  let result = run program full_outfile in
  assert_equal (Right(expected ^ "\n")) result ~printer:either_printer

let test_run_anf program_anf outfile expected test_ctxt =
  let full_outfile = "output/" ^ outfile in
  let result = run_anf program_anf full_outfile in
  assert_equal (Right(expected ^ "\n")) result ~printer:either_printer

let test_run_anf' program_str outfile expected test_ctxt =
  let program = parse_string outfile program_str in
  let result = 
      try 
        Right(Pretty.string_of_expr (anf (tag program)))
      with     
      | BindingError s -> Left("Binding error: " ^ s)
      | Failure s -> Left("Compile error: " ^ s)
      | err -> Left("Unexpected compile error: " ^ Printexc.to_string err)
  in 
  assert_equal (Right(expected ^ "\n")) result ~printer:either_printer

let test_run_input filename expected test_ctxt =
  test_run (string_of_file ("input/" ^ filename)) filename expected test_ctxt

let test_err program_str outfile errmsg test_ctxt =
  let full_outfile = "output/" ^ outfile in
  let program = parse_string outfile program_str in
  let result = run program full_outfile in
  assert_equal
    (Left(errmsg))
    result
    ~printer:either_printer
    ~cmp: (fun check result ->
      match check, result with
        | Left(expect_msg), Left(actual_message) ->
          String.exists actual_message expect_msg          
        | _ -> false
    )

let test_err_input filename expected test_ctxt =
  test_err (string_of_file ("input/" ^ filename)) filename expected test_ctxt
