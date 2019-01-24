open Printf
open Types
open Pretty

let rec is_anf (e : 'a expr) : bool =
  match e with
  | EPrim1(_, e, _) -> is_imm e
  | EPrim2(_, e1, e2, _) -> is_imm e1 && is_imm e2
  | ELet(binds, body, _) ->
     List.for_all (fun (_, e, _) -> is_anf e) binds
     && is_anf body
  | EIf(cond, thn, els, _) -> is_imm cond && is_anf thn && is_anf els
  | _ -> is_imm e
and is_imm e =
  match e with
  | ENumber _ -> true
  | EId _ -> true
  | _ -> false
;;

(* PROBLEM 1 *)
(* This function should encapsulate the binding-error checking from Adder *)
exception BindingError of string
let rec check_scope (e : (Lexing.position * Lexing.position) expr) : unit =
  failwith "check_scope: Implement this"
  
type tag = int
(* PROBLEM 2 *)
(* This function assigns a unique tag to every subexpression and let binding *)
let tag (e : 'a expr) : tag expr =
  let rec help (e : 'a expr) (cur : tag) : (tag expr * tag) =
    match e with
    | ENumber(n, _) -> (ENumber(n, cur), cur + 1)
    | EId(x, _)     -> (EId(x, cur), cur + 1)
    | EPrim1(op, e, _)       -> let (tag_e, next_tag) = help e (cur + 1) in
                                  (EPrim1(op, tag_e, cur), next_tag)
    | EPrim2 (op, e1, e2, _) -> let (tag_e1, next_tag) = help e1 (cur + 1) in
                                let (tag_e2, next_tag') = help e2 next_tag in
                                  (EPrim2(op, tag_e1, tag_e2, cur), next_tag')
    | ELet(binds, body, _)   -> let (tag_binds, next_tag) = 
                                  List.fold_left 
                                  (fun (tag_binds, cur) (x, expr, _) -> 
                                    let (tag_expr, next_tag) = help expr (cur + 1) in
                                        (tag_binds @ [(x, tag_expr, cur)], next_tag))
                                  ([], cur + 1) binds
                                in 
                                let (tag_body, next_tag') = help body next_tag in
                                  (ELet(tag_binds, tag_body, cur), next_tag')
    | EIf(cond, thn, els, _) -> let (tag_cond, next_tag) = help cond (cur + 1) in
                                let (tag_thn, next_tag') = help thn next_tag in
                                let (tag_els, next_tag'') = help els next_tag' in
                                  (EIf(tag_cond, tag_thn, tag_els, cur), next_tag'')
  in
  let (tagged, _) = help e 1 in tagged
;;


(* This function removes all tags, and replaces them with the unit value.
   This might be convenient for testing, when you don't care about the tag info. *)
let rec untag (e : 'a expr) : unit expr =
  match e with
  | EId(x, _) -> EId(x, ())
  | ENumber(n, _) -> ENumber(n, ())
  | EPrim1(op, e, _) ->
     EPrim1(op, untag e, ())
  | EPrim2(op, e1, e2, _) ->
     EPrim2(op, untag e1, untag e2, ())
  | ELet(binds, body, _) ->
     ELet(List.map(fun (x, b, _) -> (x, untag b, ())) binds, untag body, ())
  | EIf(cond, thn, els, _) ->
     EIf(untag cond, untag thn, untag els, ())

(* PROBLEM 3 & 4 *)
(* This function converts a tagged expression into an untagged expression in A-normal form *)
let anf (e : tag expr) : unit expr =
  (* The result is a pair of an answer and a context.
     The answer must be an immediate, and the context must be a list of bindings
     that are all in ANF. *)
  let rec helper (e : tag expr) : (unit expr * (string * unit expr * unit) list) =
    match e with
    | EId(x, _)          -> (EId(x, ()), [])
    | ENumber(n, _)      -> (ENumber(n, ()), [])
    | EPrim1(op, e, tag) -> let (e_anf, e_ctxt) = helper e in
                            let temp = sprintf "$eprim1_%d" tag in
                              (EId(temp, ()), 
                               e_ctxt @ (* the context needed for the expression *)
                               [(temp, EPrim1(op, e_anf, ()), ())]) (* definition of the answer *)
    | EPrim2(op, e1, e2, tag) ->  let (e1_anf, e1_ctxt) = helper e1 in
                                  let (e2_anf, e2_ctxt) = helper e2 in
                                  let temp = sprintf "$eprim2_%d" tag in
                                  (EId(temp, ()), 
                                   e1_ctxt @ (* the context needed for the left expression *)
                                   e2_ctxt @ (* the context needed for the right expression *)
                                   [(temp, EPrim2(op, e1_anf, e2_anf, ()), ())]) (* definition of the answer *)
    | ELet(binds, body, _)   -> failwith "anf let not implemented"   
    | EIf(cond, thn, els, _) -> failwith "anf if not implemented"
  in
  let (e_tag, bindings_tag) = helper e in
    ELet(bindings_tag, e_tag, ())
;;

(* Helper functions *)
let r_to_asm (r : reg) : string =
  match r with
  | EAX -> "eax"
  | ESP -> "esp"

let arg_to_asm (a : arg) : string =
  match a with
  | Const(n) -> sprintf "%d" n
  | Reg(r) -> r_to_asm r
  | RegOffset(n, r) ->
     if n >= 0 then
       sprintf "[%s+%d]" (r_to_asm r) (word_size * n)
     else
       sprintf "[%s-%d]" (r_to_asm r) (-1 * word_size * n)

let i_to_asm (i : instruction) : string =
  match i with
  | IMov(dest, value) ->
     sprintf "  mov %s, %s" (arg_to_asm dest) (arg_to_asm value)
  | IAdd(dest, to_add) ->
     sprintf "  add %s, %s" (arg_to_asm dest) (arg_to_asm to_add)
  | IRet ->
     "  ret"
  | _ -> failwith "i_to_asm: Implement this"

let to_asm (is : instruction list) : string =
  List.fold_left (fun s i -> sprintf "%s\n%s" s (i_to_asm i)) "" is

let rec find ls x =
  match ls with
  | [] -> failwith (sprintf "Name %s not found" x)
  | (y,v)::rest ->
     if y = x then v else find rest x

(* PROBLEM 5 *)
(* This function actually compiles the tagged ANF expression into assembly *)
(* The si parameter should be used to indicate the next available stack index for use by Lets *)
(* The env parameter associates identifier names to stack indices *)
let rec compile_expr (e : tag expr) (si : int) (env : (string * int) list) : instruction list =
  match e with
  | ENumber(n, _) -> [ IMov(Reg(EAX), compile_imm e env) ]
  | EId(x, _) -> [ IMov(Reg(EAX), compile_imm e env) ]
  | EPrim1(op, e, _) ->
     let e_reg = compile_imm e env in
     begin match op with
     | Add1 -> [ IMov(Reg(EAX), e_reg); IAdd(Reg(EAX), Const(1))   ]
     | Sub1 -> [ IMov(Reg(EAX), e_reg); IAdd(Reg(EAX), Const(~-1)) ]
     end
  | EPrim2(op, e1, e2, _) ->
     let e1_reg = compile_imm e1 env in
     let e2_reg = compile_imm e2 env in
     begin match op with
     | Plus  -> [ IMov(Reg(EAX), e1_reg); IAdd(Reg(EAX), e2_reg) ]
     | Minus -> [ IMov(Reg(EAX), e1_reg); ISub(Reg(EAX), e2_reg) ]
     | Times -> [ IMov(Reg(EAX), e1_reg); IMul(Reg(EAX), e2_reg) ]
     end
  | EIf(cond, thn, els, tag) ->
     failwith "compile_expr:eif: Implement this"
  | ELet([id, e, _], body, _) ->
     failwith "compile_expr:elet: Implement this"
  | _ -> failwith "Impossible: Not in ANF"
and compile_imm e env =
  match e with
  | ENumber(n, _) -> Const(n)
  | EId(x, _) -> RegOffset(~-(find env x), ESP)
  | _ -> failwith "Impossible: not an immediate"


let compile_anf_to_string anfed =
  let prelude =
    "section .text
global our_code_starts_here
our_code_starts_here:" in
  let compiled = (compile_expr anfed 1 []) in
  let as_assembly_string = (to_asm (compiled @ [IRet])) in
  sprintf "%s%s\n" prelude as_assembly_string

    
let compile_to_string prog =
  check_scope prog;
  let tagged : tag expr = tag prog in
  let anfed : tag expr = tag (anf tagged) in
  (* printf "Prog:\n%s\n" (ast_of_expr prog); *)
  (* printf "Tagged:\n%s\n" (format_expr tagged string_of_int); *)
  (* printf "ANFed/tagged:\n%s\n" (format_expr anfed string_of_int); *)
  compile_anf_to_string anfed

