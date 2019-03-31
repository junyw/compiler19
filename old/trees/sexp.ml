open Unix
open Str
open Printf

type 'a tok =
  | LPAREN of 'a
  | RPAREN of 'a
  | TSym of string * 'a
  | TInt of int * 'a
  | TBool of bool * 'a
let tok_info t =
  match t with
  | LPAREN x -> x
  | RPAREN x -> x
  | TSym (_, x) -> x
  | TInt (_, x) -> x
  | TBool (_, x) -> x
;;

(* startline, startcol, endline, endcol *)
type pos = int * int * int * int
let pos_to_string (startline, startcol, endline, endcol) range =
  if range then
    Printf.sprintf "line %d, col %d--line %d, col %d" startline startcol endline endcol
  else
    Printf.sprintf "line %d, col %d" startline startcol
;;

(* tokenize: a lexer that converts the given string to a list of tokens *)
let tokenize (str : string) : pos tok list =
  (* fold_left consumes one split_result at each step and update the accumulator *)
  (* The accumulator consists of a list of token, an integer for line number, and an integer for column number *)
  let (toks, _, _) = List.fold_left
    (* takes a split_result, and convert it to the corresponding token, and updates the line number and column number *)
    (fun ((toks : pos tok list), (line : int), (col : int)) (tok : Str.split_result) ->
      match tok with
      | Delim t ->
         if t = " " then (toks, line, col + 1)
         else if t = "\t" then (toks, line, col + 1)
         else if t = "\n" then (toks, line + 1, 0)
         else if t = "(" then (LPAREN (line, col, line, col + 1) :: toks, line, col + 1)
         else if t = ")" then (RPAREN (line, col, line, col + 1) :: toks, line, col + 1)
         else
           let tLen = String.length t
           in ((TSym (t, (line, col, line, col + tLen))) :: toks, line, col + tLen)
      | Text t ->
         if t = "true" then (TBool (true, (line, col, line, col + 4)) :: toks, line, col + 4)
         else if t = "false" then (TBool (false, (line, col, line, col + 5)) :: toks, line, col + 5)
         else
           let tLen = String.length t
           in try ((TInt (int_of_string t, (line, col, line, col + tLen))) :: toks, line, col + tLen) with
              | Failure _ -> (TSym (t, (line, col, line, col + tLen)) :: toks, line, col + tLen)
    )
    (* Initial state of the accumulator *)
    ([], 0, 0)
    (* Split the string by delimiters "(", ")", "\n", "\t" or space. *)
    (full_split (regexp "[()\n\t ]") str)
  in List.rev toks
;;

type 'a sexp =
  | Sym of string * 'a
  | Int of int * 'a
  | Bool of bool * 'a
  | Nest of 'a sexp list * 'a
let sexp_info s =
  match s with
  | Sym (_, x) -> x
  | Int (_, x) -> x
  | Bool (_, x) -> x
  | Nest (_, x) -> x
;;

type 'a scope = 'a sexp list * 'a

(* parse_toks : given a list of tokens, returns a S-expression or an error *)
let parse_toks (toks : pos tok list) : (pos sexp list, string) result =
  (* close_scope : given a scope and an info at the end of the scope, returns a Nest sexp *)
  let close_scope ((sexps, (a0, a1, _, _)) : pos scope) ((_, _, b2, b3) : pos) : pos sexp =
        Nest(sexps, (a0, a1, b2, b3))
  (* add_to_scope : given a scope and a sexp, returns a new scope *)
  and add_to_scope ((sexps, info) : pos scope) (sexp : pos sexp) : pos scope = 
        (sexps@[sexp], info) 
  in
  let parse_tok ((sexps, info as current_scope : pos scope), (stack : pos sexp Stack.t)) (token : pos tok) : (pos scope * pos sexp Stack.t) = 
    match token with 
    | LPAREN (start_info) -> Stack.push (Nest (sexps, info)) stack;
                             (([], start_info), stack)                             
    | RPAREN (end_info)   -> if Stack.is_empty stack then failwith ("Unmatched right paren at " ^ (pos_to_string end_info false))
                             else let Nest (sexps, info) = Stack.pop stack in
                             (add_to_scope (sexps, info) (close_scope current_scope end_info), stack)
    | TSym (name, info)   -> (add_to_scope current_scope (Sym(name, info)), stack)
    | TInt (value, info)  -> (add_to_scope current_scope (Int(value, info)), stack)
    | TBool (value, info) -> (add_to_scope current_scope (Bool(value, info)), stack)
  in 
  let parse_toks' (toks : pos tok list) : pos sexp list = 
    let (sexps, info), stack = List.fold_left parse_tok ((* dummy scope *)([], (-1,-1,-1,-1)), Stack.create ()) toks in
    if Stack.is_empty stack then sexps
    else failwith ("Unmatched left paren at " ^ (pos_to_string info false))
  in
    try  Ok (parse_toks' toks) 
    with Failure(msg) -> Error msg
;;

let parse (str : string) : (pos sexp list, string) result = 
  parse_toks (tokenize str)
;;
