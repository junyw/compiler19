open Printf
open Sexp

(* Abstract syntax of (a small subset of) x86 assembly instructions *)

type reg =
  | EAX
  | ESP

type arg =
  | Const of int
  | Reg of reg
  | RegOffset of int * reg (* int is # words of offset *)

type instruction =
  | IMov of arg * arg
  | IAdd of arg * arg
  | IRet

(* Concrete syntax of the Adder language:

‹expr›:
  | NUMBER
  | IDENTIFIER
  | ( let ( ‹bindings› ) ‹expr› )
  | ( add1 ‹expr› )
  | ( sub1 ‹expr› )
‹bindings›:
  | ( IDENTIFIER ‹expr› )
  | ( IDENTIFIER ‹expr› ) ‹bindings›

 *)


(* Abstract syntax of the Adder language *)

type prim1 =
  | Add1
  | Sub1

type 'a expr =
  | Number of int * 'a
  | Id of string * 'a
  | Let of (string * 'a expr) list * 'a expr * 'a
  | Prim1 of prim1 * 'a expr * 'a

(* Function to convert from unknown s-expressions to Adder exprs
   Throws a SyntaxError message if there's a problem
 *)
exception SyntaxError of string
let rec expr_of_sexp (s : pos sexp)  : pos expr = (* rec ? *)
  let process_bindings bindings =
    List.fold_left 
    (fun exprs sexp -> match sexp with 
                       | Nest([Sym(x, _);expr], info) -> 
                          let let_expr = (x, (expr_of_sexp expr)) in
                              exprs@[let_expr]
                       | _ -> raise (SyntaxError "unknown syntax")
    )
    []
    bindings
  in
  match s with 
  | Sym(id, info)     -> Id (id, info)
  | Int(n, info)      -> Number (n, info)
  | Bool(value, info) -> failwith (sprintf "Bool sexp not yet implemented at pos %s"
                    (pos_to_string (sexp_info s) true))
  | Nest(sexps, info) -> 
      match sexps with 
      | [Sym("let", info);Nest(bindings, _);b] -> 
        let exprs = process_bindings bindings in
          Let (exprs, (expr_of_sexp b), info)
      | [Sym("add1", info);b] -> Prim1 (Add1, (expr_of_sexp b), info)
      | [Sym("sub1", info);b] -> Prim1 (Sub1, (expr_of_sexp b), info)
      | Sym(id, info)::rest -> (match id with 
                             |  _ -> failwith ("unknown IDENTIFIER of " ^ id))
      | _ -> failwith (sprintf "not yet implemented at pos %s"
                    (pos_to_string (sexp_info s) true))


(* Functions that implement the compiler *)

(* The next four functions convert assembly instructions into strings,
   one datatype at a time.  Only one function has been fully implemented
   for you. *)
let reg_to_asm_string (r : reg) : string =
  match r with
  | EAX -> "eax"
  | ESP -> "esp"

let arg_to_asm_string (a : arg) : string =
  match a with
  | Const(n) -> sprintf "%d" n
  | Reg(r)   -> reg_to_asm_string r
  | RegOffset(n, r) -> sprintf "[%s-4*%d]" (reg_to_asm_string r) n


let instruction_to_asm_string (i : instruction) : string =
  match i with
  | IMov(dest, value) ->
     sprintf "\tmov %s, %s" (arg_to_asm_string dest) (arg_to_asm_string value)
  | IAdd(dest, value) -> 
    sprintf "\tadd %s, %s" (arg_to_asm_string dest) (arg_to_asm_string value)
  | IRet -> "\tret"

let to_asm_string (is : instruction list) : string =
  List.fold_left (fun s i -> sprintf "%s\n%s" s (instruction_to_asm_string i)) "" is

(* A helper function for looking up a name in a "dictionary" and 
   returning the associated value if possible.  This is definitely
   not the most efficient data structure for this, but it is nice and simple... *)
let rec find (ls : (string * 'a) list) (x : string) : 'a option =
  match ls with
  | [] -> None
  | (y, v)::rest ->
     if y = x then Some(v) else find rest x

let add name (env : (string * 'a) list) : ((string * 'a) list * int) =
  let slot = 1 + (List.length env) in
    ((name, slot)::env, slot)

(* The exception to be thrown when some sort of problem is found with names *)
exception BindingError of string
(* The actual compilation process.  The `compile` function is the primary function,
   and uses `compile_env` as its helper.  In a more idiomatic OCaml program, this
   helper would likely be a local definition within `compile`, but separating it out
   makes it easier for you to test it. *)
let rec compile_env
          (p : pos expr)         (* the program, currently annotated with source location info *)
          (stack_index : int)    (* the next available stack index *)
          (env : (string * int) list) (* the current binding environment of names to stack slots *)
        : instruction list =     (* the instructions that would execute this program *)
  let compile_bindings (bindings : (string * 'a expr) list) env =
    List.fold_left 
    (fun (env, instrs) binding -> match binding with 
                       | (x, expr) -> 
                          (* Compile the binding, and get the result into EAX *)
                          let let_instrs = (compile_env expr stack_index env) in
                          let (env', slot) = add x env in
                              (env',  instrs
                                    @ let_instrs
                                    (* Copy the result in EAX into the appropriate stack slot *)
                                    @ [ IMov (RegOffset(slot, ESP), Reg(EAX)) ])  
                       | _ -> failwith "not implemented"
    )
    (env, [])
    bindings
  in
  match p with
  | Number(n, _) ->
     [ IMov(Reg(EAX), Const(n)) ]
  | Id(id, _) ->
      (match (find env id) with 
      | Some(v) -> [ IMov(Reg(EAX), RegOffset(v, ESP)) ]
      | None    -> failwith "id not in scope...")
  | Let(bindings, body, _) -> 
      let (env', instrs) = compile_bindings bindings env in 
        (* Compile the body, given that variables are in the correct slot when it's needed *)
        instrs @ (compile_env body stack_index env')
  | Prim1(prim, arg , _) ->
     (match prim with 
      | Add1 -> (compile_env arg stack_index env)(* fix *) @ [ IAdd(Reg(EAX), Const(1)) ]
      | Sub1 -> (compile_env arg stack_index env)(* fix *) @ [ IAdd(Reg(EAX), Const(-1)) ])

let compile (p : pos expr) : instruction list =
  compile_env p 1 [] (* Start at the first stack slot, with an empty environment *)

(* The entry point for the compiler: a function that takes a expr and
   creates an assembly-program string representing the compiled version *)
let compile_to_string (prog : pos expr) : string =
  let prelude = "
section .text
global our_code_starts_here
our_code_starts_here:" in
  let asm_string = (to_asm_string ((compile prog) @ [IRet])) in
  let asm_program = sprintf "%s%s\n" prelude asm_string in
  asm_program

