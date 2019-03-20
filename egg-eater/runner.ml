open Unix
open Filename
open Str
open Compile
open Printf
open OUnit2
open ExtLib
open Lexing
open Exprs
open Pretty
open Phases
open Errors

let result_printer (e : (string, string) result) : string =
  match e with
  | Error(v) -> sprintf "Error: %s\n" v
  | Ok(v) -> v

let parse (name : string) lexbuf : sourcespan program  =
  try 
    lexbuf.lex_curr_p <- { lexbuf.lex_curr_p with pos_fname = name };
    Parser.program Lexer.token lexbuf
  with
  | (Failure msg) as exn ->
     if msg = "lexing: empty token" then
       raise (ParseError (sprintf "Lexical error at %s" (string_of_position lexbuf.lex_curr_p)))
     else
       let bt = Printexc.get_raw_backtrace () in
       Printexc.raise_with_backtrace exn bt (* make sure we throw with the same stack trace *)
  | Parsing.Parse_error ->
     begin
       let curr = lexbuf.Lexing.lex_curr_p in
       let line = curr.Lexing.pos_lnum in
       let cnum = curr.Lexing.pos_cnum - curr.Lexing.pos_bol in
       let tok = Lexing.lexeme lexbuf in
       raise (ParseError (sprintf "Parse error at line %d, col %d: token `%s`"
                            line cnum tok))
     end

(* Read a file into a string *)
let string_of_file (file_name : string) : string =
  let inchan = open_in file_name in
  really_input_string inchan (in_channel_length inchan)

let parse_string (name : string) (s : string) : sourcespan program = 
  let lexbuf = Lexing.from_string s in
  parse name lexbuf

let parse_file (name : string) input_file : sourcespan program = 
  let lexbuf = Lexing.from_channel input_file in
  parse name lexbuf

let compile_string_to_string (name : string) (input : string) : string pipeline =
  (Ok(input, [])
   |> add_phase source (fun x -> x)
   |> add_err_phase parsed (fun input ->
          try Ok(parse_string name input)
          with err -> Error([err])))
  |> compile_to_string;;

let compile_file_to_string (name : string) (input_file : string) : string pipeline =
  compile_string_to_string name (string_of_file input_file)

let make_tmpfiles (name : string) (std_input : string) =
  let (stdin_read, stdin_write) = pipe() in
  let stdout_name = (temp_file ("stdout_" ^ name) ".out") in
  let stderr_name = (temp_file ("stderr_" ^ name) ".err") in
  ignore(Unix.write_substring stdin_write std_input 0 (String.length std_input));
  Unix.close(stdin_write);
  (openfile stdout_name [O_RDWR] 0o600, stdout_name,
   openfile stderr_name [O_RDWR] 0o600, stderr_name,
   stdin_read)

let run_no_vg (program_name : string) args std_input : (string, string) result =
  let (rstdout, rstdout_name, rstderr, rstderr_name, rstdin) = make_tmpfiles "run" std_input in
  let ran_pid = Unix.create_process (program_name ^ ".run") (Array.of_list ([""] @ args)) rstdin rstdout rstderr in
  let (_, status) = waitpid [] ran_pid in
  let result = match status with
    | WEXITED 0 -> Ok(string_of_file rstdout_name)
    | WEXITED n -> Error(sprintf "Error %d: %s" n (string_of_file rstderr_name))
    | WSIGNALED n ->
       Error(sprintf "Signalled with %d while running %s." n program_name)
    | WSTOPPED n ->
       Error(sprintf "Stopped with signal %d while running %s." n program_name) in
  List.iter close [rstdout; rstderr; rstdin];
  List.iter unlink [rstdout_name; rstderr_name];
  result


let run_vg (program_name : string) args std_input : (string, string) result =
  let (rstdout, rstdout_name, rstderr, rstderr_name, rstdin) = make_tmpfiles "run" std_input in
  let ran_pid = Unix.create_process "valgrind"  (Array.of_list ([""; (program_name ^ ".run")] @ args)) rstdin rstdout rstderr in
  let (_, status) = waitpid [] ran_pid in
  let vg_str = string_of_file rstderr_name in
  let vg_ok = String.exists vg_str "0 errors from 0 contexts" in
  let result = match (status, vg_ok) with
    | WEXITED 0, true -> Ok(string_of_file rstdout_name)
    | WEXITED 0, false -> Error("Stdout: " ^ (string_of_file rstdout_name) ^ "\n" ^ "Valgrind: \n" ^ vg_str)
    | WEXITED n, _ -> Error(sprintf "Error %d: %s" n vg_str)
    | WSIGNALED n, _ ->
       Error(sprintf "Signalled with %d while running %s." n program_name)
    | WSTOPPED n, _ ->
       Error(sprintf "Stopped with signal %d while running %s." n program_name) in
  List.iter close [rstdout; rstderr; rstdin];
  List.iter unlink [rstdout_name; rstderr_name];
  result



let run_asm (asm_string : string) (out : string) (runner : string -> string list -> string -> (string, string) result) args (std_input : string) =
  let outfile = open_out (out ^ ".s") in
  fprintf outfile "%s" asm_string;
  close_out outfile;
  let (bstdout, bstdout_name, bstderr, bstderr_name, bstdin) = make_tmpfiles "build" "" in
  let built_pid = Unix.create_process "make" (Array.of_list [""; out ^ ".run"]) bstdin bstdout bstderr in
  let (_, status) = waitpid [] built_pid in

  let try_running = match status with
    | WEXITED 0 ->
       Ok(string_of_file bstdout_name)
    | WEXITED n ->
       Error(sprintf "Finished with error while building %s:\n%s" out (string_of_file bstderr_name))
    | WSIGNALED n ->
       Error(sprintf "Signalled with %d while building %s." n out)
    | WSTOPPED n ->
       Error(sprintf "Stopped with signal %d while building %s." n out) in

  let result = match try_running with
    | Error(_) -> try_running
    | Ok(msg) ->
       runner out args std_input in

  List.iter close [bstdout; bstderr; bstdin];
  List.iter unlink [bstdout_name; bstderr_name];
  result


let run (p : sourcespan program) (out : string) runner args std_input : (string, string) result =
  let maybe_asm_string = compile_to_string (Ok(p, [])) in
  match maybe_asm_string with
  | Error(errs, _) -> Error(ExtString.String.join "\n" (print_errors errs))
  | Ok(asm_string, _) ->
     run_asm asm_string out runner args std_input

let run_anf p out runner args std_input =
  let maybe_asm_string =
    try Ok(compile_prog p) with
    | Failure s -> Error([Failure("Compile error: " ^ s)])
    | err -> Error([Failure("Unexpected compile error: " ^ Printexc.to_string err)])
  in    
  match maybe_asm_string with
  | Error(errs) -> Error(ExtString.String.join "\n" (print_errors errs))
  | Ok(asm_string) ->
     run_asm asm_string out runner args std_input


let test_run program_str outfile expected test_ctxt =
  let full_outfile = "output/" ^ outfile in
  let program = parse_string outfile program_str in
  let result = run program full_outfile run_no_vg [] "" in
  assert_equal (Ok(expected ^ "\n")) result ~printer:result_printer

(* test run with input *)
let test_run_stdin args std_input program_str outfile expected test_ctxt =
  let full_outfile = "output/" ^ outfile in
  let program = parse_string outfile program_str in
  let result = run program full_outfile run_no_vg args std_input in
  assert_equal (Ok(expected ^ "\n")) result ~printer:result_printer

let test_run_anf program_anf outfile expected test_ctxt =
  let full_outfile = "output/" ^ outfile in
  let result = run_anf program_anf full_outfile run_no_vg [] "" in
  assert_equal (Ok(expected ^ "\n")) result ~printer:result_printer

let test_run_valgrind program_str outfile expected test_ctxt =
  let full_outfile = "output/" ^ outfile in
  let program = parse_string outfile program_str in
  let result = run program full_outfile run_vg [] "" in
  assert_equal (Ok(expected ^ "\n")) result ~printer:result_printer

let test_err program_str outfile errmsg test_ctxt =
  let full_outfile = "output/" ^ outfile in
  let program = parse_string outfile program_str in
  let result = run program full_outfile run_no_vg [] "" in
  assert_equal
    (Error(errmsg))
    result
    ~printer:result_printer
    ~cmp: (fun check result ->
      match check, result with
      | Error(expect_msg), Error(actual_message) ->
         String.exists actual_message expect_msg
      | _ -> false
    )

    
let test_run_input filename expected test_ctxt =
  test_run (string_of_file ("input/" ^ filename)) filename expected test_ctxt

let test_err_input filename expected test_ctxt =
  test_err (string_of_file ("input/" ^ filename)) filename expected test_ctxt
