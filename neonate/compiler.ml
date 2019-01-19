open Printf

type expr = 
	| Num of int
	| Add1 of expr
	| Sub1 of expr
	| Id of string
	| Let of string * expr * expr

type reg = 
	| EAX
	| ESP (* the stack pointer, below which we can use memory *)

type env = (string * int) list

fun lookup name env = 
	match env with 
	| [] -> failwith (sprintf "Identifier %s not found in environment" name)
	| (n, i)::rest ->
		if n = name then i else (lookup name rest)

fun add name env : (env * int) =
	let slot = 1 + (List.length env) in
		((name, slot)::env, slot)

type arg = 
	| Const of int
	| Reg of reg
	| RegOffset of reg * int (* RegOffset(reg, i) represents address [reg + 4*i] *)

type instruction = 
	| IMov of arg * arg
	| IAdd of arg * arg

let asm_to_string (asm : instruction list) : string = 
;;

let compile_expr (exp : expr) (env : env) : instruction list = 
	match exp with
	| Num n -> [ IMov(Reg(EAX), Const(n)) ]
	| Add1 e -> (compile_expr e) @ [ IAdd(Reg(EAX), Const(1)) ]
	| Sub1 e -> (compile_expr e) @ [ IAdd(Reg(EAX), Const(-1)) ]
	| Let(x, e, b) -> 
		let (env', slot) = add x env in
			(compile e env) @
			[ IMov(RegOffset(ESP, slot), Reg(EAX)) ] @
			(compile b env')
;;

let compile_prog (e : expr) : string =
	let instrs = compile_expr e in
	let asm_string = asm_to_string instrs in
	let prelude = "
section .text
global our_code_starts_here
our_code_starts_here:" in
	let suffix = "ret" in
	prelude ^ "\n" ^ asm_string ^ "\n" ^ suffix
;;

(*let compile (program : int) : string = 
	sprintf "
section .text
global our_code_starts_here
our_code_starts_here:
	mov eax, %d
	ret\n" program
*)
(* Some OCaml boilerplate for reading files and command-line arguments *)
let () = 
	let input_file = (open_in (Sys.argv.(1))) in
	let input_program = int_of_string (input_line input_file) in
	let program = (compile input_program) in
	printf "%s\n" program
;;