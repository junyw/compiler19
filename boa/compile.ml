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
  (* TODO: implement me *)
  ()
  
type tag = int
(* PROBLEM 2 *)
(* This function assigns a unique tag to every subexpression and let binding *)
let tag (e : 'a expr) : tag expr =
  let rec help (e : 'a expr) (cur : tag) : (tag expr * tag) =
    match e with
    | ENumber(n, _) -> (ENumber(n, cur), cur + 1)
    | EId(x, _)     -> (EId(x, cur), cur + 1)
    | EPrim1(op, e, _)      -> let (tag_e, next_tag) = help e (cur + 1) in
                                   (EPrim1(op, tag_e, cur), next_tag)
    | EPrim2(op, e1, e2, _) -> let (tag_e1, next_tag) = help e1 (cur + 1) in
                               let (tag_e2, next_tag') = help e2 next_tag in
                                   (EPrim2(op, tag_e1, tag_e2, cur), next_tag')
    | ELet(binds, body, _)  -> let (tag_binds, next_tag) = 
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
                            let temp = sprintf "$prim1_%d" tag in
                              (EId(temp, ()), 
                               e_ctxt (* the context needed for the expression *)
                               @ [(temp, EPrim1(op, e_anf, ()), ())]) (* definition of the answer *)
    | EPrim2(op, e1, e2, tag) ->  let (e1_anf, e1_ctxt) = helper e1 in
                                  let (e2_anf, e2_ctxt) = helper e2 in
                                  let temp = sprintf "$prim2_%d" tag in
                                  (EId(temp, ()), 
                                   e1_ctxt (* the context needed for the left expression *)
                                   @ e2_ctxt (* the context needed for the right expression *)
                                   @ [(temp, EPrim2(op, e1_anf, e2_anf, ()), ())]) (* definition of the answer *)
    | ELet(binds, body, tag)   -> let (binds_anf, binds_ctxt) =
                                      List.fold_left 
                                      (fun (b_anfs, b_ctxts) (x, expr, _) -> 
                                           let (b_anf, b_ctxt) = helper expr in
                                               (b_anfs @ [(x, b_anf, ())], b_ctxts @ b_ctxt))
                                      ([], []) binds 
                                  in
                                  let (body_anf, body_ctxt) = helper body in
                                  (ELet(binds_anf, body_anf, ()), 
                                    binds_ctxt
                                    @ body_ctxt)
    | EIf(cond, thn, els, tag) -> let (cond_anf, cond_ctxt) = helper cond in
                                  let (thn_anf, thn_ctxt) = helper thn in
                                  let (els_anf, els_ctxt) = helper els in
                                  let temp = sprintf "$if_%d" tag in
                                    (EId(temp, ()), 
                                     cond_ctxt
                                     @ thn_ctxt 
                                     @ els_ctxt 
                                     @ [(temp, EIf(cond_anf, thn_anf, els_anf, ()), ())])
  in
  let (e_tag, bindings_tag) = helper e in
    if List.length bindings_tag = 0 then e_tag 
    else ELet(bindings_tag, e_tag, ())
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
  | IAdd(dest, value) ->
     sprintf "  add %s, %s" (arg_to_asm dest) (arg_to_asm value)
  | ISub(dest, value) ->
     sprintf "  sub %s, %s" (arg_to_asm dest) (arg_to_asm value)
  | IMul(dest, value) ->
     sprintf "  imul %s, %s" (arg_to_asm dest) (arg_to_asm value)
  | ILabel(label)     -> 
     sprintf "%s:" label
  | ICmp(val1, val2)  -> 
     sprintf "  cmp %s, %s" (arg_to_asm val1) (arg_to_asm val2)
  | IJne(label) -> 
     sprintf "  jne %s" label
  | IJe(label)  -> 
     sprintf "  je %s" label
  | IJmp(label) -> 
     sprintf "  jmp %s" label
  | IRet ->
     "  ret"

let to_asm (is : instruction list) : string =
  List.fold_left (fun s i -> sprintf "%s\n%s" s (i_to_asm i)) "" is

let rec find ls x =
  match ls with
  | [] -> failwith (sprintf "Name %s not found" x)
  | (y,v)::rest ->
     if y = x then v else find rest x

let add (env : (string * 'a) list) (x : string) : ((string * 'a) list * int) =
  let slot = 1 + (List.length env) in
    ((x, slot)::env, slot)

(* PROBLEM 5 *)
(* This function actually compiles the tagged ANF expression into assembly *)
(* The si parameter should be used to indicate the next available stack index for use by Lets *)
(* The env parameter associates identifier names to stack indices *)
let rec compile_expr (e : tag expr) (si : int) (env : (string * int) list) : instruction list =
  let compile_imm e env : arg =
    match e with
    | ENumber(n, _) -> Const(n)
    | EId(x, _) -> RegOffset(~-(find env x), ESP)
    | _ -> failwith "Impossible: not an immediate"
  in
  let compile_bindings (bindings : (string * 'a expr * 'a) list) env =
    List.fold_left 
    (fun (env, instrs) ((x, expr, _) : (string * 'a expr * 'a)) -> 
      (* Compile the binding, and get the result into EAX *)
      let let_instrs = (compile_expr expr si env) in
      let (env', slot) = add env x in
          (env', instrs
               @ let_instrs
               (* Copy the result in EAX into the appropriate stack slot *)
               @ [ IMov (RegOffset(~-slot, ESP), Reg(EAX)) ])  
    )
    (env, [])
    bindings
  in  
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
    let else_label = sprintf "if_false_%d" tag in
    let done_label = sprintf "done_%d" tag in
      ( compile_expr cond si env )
      @ [ ICmp(Reg(EAX), Const(0)); IJe(else_label) ]
      @ ( compile_expr thn si env )
      @ [ IJmp(done_label); ILabel(else_label) ]
      @ ( compile_expr els si env )
      @ [ ILabel(done_label) ]
  | ELet(bindings, body, _) -> 
      let (env', instrs) = compile_bindings bindings env in 
        (* Compile the body, given that variables are in the correct slot when it's needed *)
        instrs @ (compile_expr body si env')

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

