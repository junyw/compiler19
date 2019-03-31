open Unix
open Filename
open Str
open Compile
open Printf
open OUnit2
open ExtLib
open Sexp
       
type ('a, 'b) either =
  | Left of 'a
  | Right of 'b

let either_printer (e : (string, string) either) : string =
  match e with
    | Left(v) -> sprintf "Error: %s\n" v
    | Right(v) -> v

                    
(* Read a file into a string *)
let string_of_file (file_name : string) : string =
  let inchan = open_in file_name in
  really_input_string inchan (in_channel_length inchan)

let parse_string (s : string) : pos expr = Compile.expr_of_sexp (Sexp.parse s)
    
let compile_string_to_string (s : string) : string =
  let input_program = parse_string s in
  (compile_to_string input_program);;

let compile_file_to_string (input_file : string) : string =
  compile_string_to_string (string_of_file input_file);;

type tempfiles = Unix.file_descr * string (* stdout file and name *)
               * Unix.file_descr * string (* stderr file and name *)
               * Unix.file_descr (* stdin file *)
let make_tmpfiles (name : string) : tempfiles =
  let (null_stdin, _) = pipe() in
  let stdout_name = (temp_file ("stdout_" ^ name) ".out") in
  let stderr_name = (temp_file ("stderr_" ^ name) ".err") in
  (openfile stdout_name [O_RDWR] 0o600, stdout_name,
   openfile stderr_name [O_RDWR] 0o600, stderr_name,
   null_stdin)

let run (p : pos expr) (out : string) : (string, string) either =
  let maybe_asm_string =
    try Right(compile_to_string p)
    with Failure s -> 
      Left("Compile error: " ^ s)
  in    
  match maybe_asm_string with
  | Left(s) -> Left(s)
  | Right(asm_string) ->
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


let test_run (program_str : string) (outfile : string) (expected : string) (test_ctxt : OUnit2.test_ctxt) : unit =
  let full_outfile = "output/" ^ outfile in
  let program = parse_string program_str in
  let result = run program full_outfile in
  assert_equal (Right(expected ^ "\n")) result ~printer:either_printer

let test_err (program_str : string) (outfile : string) (errmsg : string) (test_ctxt : OUnit2.test_ctxt) : unit =
  let result =
    try
      let full_outfile = "output/" ^ outfile in
      let program = parse_string program_str in
      run program full_outfile
    with Failure s -> Left(s)
       | err -> Left(Printexc.to_string err)
  in
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
