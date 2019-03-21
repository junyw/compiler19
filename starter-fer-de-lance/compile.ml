open Printf
open Pretty
open Phases
open Exprs
open Assembly
open Errors
(* Add at least one of these two *)
(* open TypeCheck *)
(* open Inference *)
       
type 'a envt = (string * 'a) list

let skip_typechecking = ref false

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
  | EBool _ -> true
  | EId _ -> true
  | _ -> false
;;


let const_true = HexConst (0xFFFFFFFF)
let const_false = HexConst(0x7FFFFFFF)
let bool_mask = HexConst(0x80000000)
let tag_as_bool = HexConst(0x00000001)

let err_COMP_NOT_NUM   = 0
let err_ARITH_NOT_NUM  = 1
let err_LOGIC_NOT_BOOL = 2
let err_IF_NOT_BOOL    = 3
let err_OVERFLOW       = 4



(* You may find some of these helpers useful *)
let rec find ls x =
  match ls with
  | [] -> raise (InternalCompilerError (sprintf "Name %s not found" x))
  | (y,v)::rest ->
     if y = x then v else find rest x

let count_vars e =
  let rec helpA e =
    match e with
    | ASeq(e1, e2, _) -> max (helpC e1) (helpA e2)
    | ALet(_, bind, body, _) -> 1 + (max (helpC bind) (helpA body))
    | ALetRec(binds, body, _) ->
       (List.length binds) + List.fold_left max (helpA body) (List.map (fun (_, rhs) -> helpC rhs) binds)
    | ACExpr e -> helpC e
  and helpC e =
    match e with
    | CIf(_, t, f, _) -> max (helpA t) (helpA f)
    | _ -> 0
  in helpA e

let rec replicate x i =
  if i = 0 then []
  else x :: (replicate x (i - 1))


let rec find_decl (ds : 'a decl list) (name : string) : 'a decl option =
  match ds with
    | [] -> None
    | (DFun(fname, _, _, _, _) as d)::ds_rest ->
      if name = fname then Some(d) else find_decl ds_rest name

let rec find_one (l : 'a list) (elt : 'a) : bool =
  match l with
    | [] -> false
    | x::xs -> (elt = x) || (find_one xs elt)

let rec find_dup (l : 'a list) : 'a option =
  match l with
    | [] -> None
    | [x] -> None
    | x::xs ->
      if find_one xs x then Some(x) else find_dup xs
;;

let rename_and_tag (p : tag program) : tag program =
  let rec rename env p =
    match p with
    | Program(tydecls, decls, body, tag) ->
       Program(tydecls, List.map (fun g -> List.map (helpD env) g) decls, helpE env body, tag)
  and helpD env decl =
    match decl with
    | DFun(name, args, scheme, body, tag) ->
       let (newArgs, env') = helpBS env args in
       DFun(name, newArgs, scheme, helpE env' body, tag)
  and helpB env b =
    match b with
    | BBlank(typ, tag) -> (b, env)
    | BName(name, typ, tag) ->
       let name' = sprintf "%s_%d" name tag in
       (BName(name', typ, tag), (name, name') :: env)
    | BTuple(binds, tag) ->
       let (binds', env') = helpBS env binds in
       (BTuple(binds', tag), env')
  and helpBS env (bs : tag bind list) =
    match bs with
    | [] -> ([], env)
    | b::bs ->
       let (b', env') = helpB env b in
       let (bs', env'') = helpBS env' bs in
       (b'::bs', env'')
  and helpBG env (bindings : tag binding list) =
    match bindings with
    | [] -> ([], env)
    | (b, e, a)::bindings ->
       let (b', env') = helpB env b in
       let e' = helpE env' e in
       let (bindings', env'') = helpBG env' bindings in
       ((b', e', a)::bindings', env'')
  and helpE env e =
    match e with
    | EAnnot(e, t, tag) -> helpE env e
    | ESeq(e1, e2, tag) -> ESeq(helpE env e1, helpE env e2, tag)
    | ETuple(es, tag) -> ETuple(List.map (helpE env) es, tag)
    | EGetItem(e, idx, len, tag) -> EGetItem(helpE env e, idx, len, tag)
    | ESetItem(e, idx, len, newval, tag) -> ESetItem(helpE env e, idx, len, helpE env newval, tag)
    | EPrim1(op, arg, tag) -> EPrim1(op, helpE env arg, tag)
    | EPrim2(op, left, right, tag) -> EPrim2(op, helpE env left, helpE env right, tag)
    | EIf(c, t, f, tag) -> EIf(helpE env c, helpE env t, helpE env f, tag)
    | ENumber _ -> e
    | EBool _ -> e
    | ENil _ -> e
    | EId(name, tag) ->
       (try
         EId(find env name, tag)
       with Not_found -> e)
    | EApp(name, args, tag) -> EApp(name, List.map (helpE env) args, tag)
    | ELet(binds, body, tag) ->
       let (binds', env') = helpBG env binds in
       let body' = helpE env' body in
       ELet(binds', body', tag)
    | ELetRec(bindings, body, tag) ->
       let (revbinds, env) = List.fold_left (fun (revbinds, env) (b, e, t) ->
                                 let (b, env) = helpB env b in ((b, e, t)::revbinds, env)) ([], env) bindings in
       let bindings' = List.fold_left (fun bindings (b, e, tag) -> (b, helpE env e, tag)::bindings) [] revbinds in
       let body' = helpE env body in
       ELetRec(bindings', body', tag)
    | ELambda(binds, body, tag) ->
       let (binds', env') = helpBS env binds in
       let body' = helpE env' body in
       ELambda(binds', body', tag)
  in (rename [] p)
;;



(* IMPLEMENT EVERYTHING BELOW *)

(* This data type lets us keep track of how a binding was introduced.
   We'll use it to discard unnecessary Seq bindings, and to distinguish 
   letrec from let. Essentially, it accumulates just enough information 
   in our binding list to tell us how to reconstruct an appropriate aexpr. *)
type 'a anf_bind =
  | BSeq of 'a cexpr
  | BLet of string * 'a cexpr
  | BLetRec of (string * 'a cexpr) list

let anf (p : tag program) : unit aprogram =
  let rec helpP (p : tag program) : unit aprogram =
    match p with
    | Program(_, decls, body, _) -> AProgram(List.concat(List.map helpG decls), helpA body, ())
  and helpG (g : tag decl list) : unit adecl list =
    List.map helpD g
  and helpD (d : tag decl) : unit adecl =
    match d with
    | DFun(name, args, ret, body, _) ->
       let args = List.map (fun a ->
                      match a with
                      | BName(a, _, _) -> a
                      | _ -> raise (InternalCompilerError("Tuple bindings should have been desugared away"))) args in
       ADFun(name, args, helpA body, ())
  and helpC (e : tag expr) : (unit cexpr * unit anf_bind list) = 
    match e with
    | EAnnot(e, _, _) -> helpC e
    | EPrim1(op, arg, _) ->
       let (arg_imm, arg_setup) = helpI arg in
       (CPrim1(op, arg_imm, ()), arg_setup)
    | EPrim2(op, left, right, _) ->
       let (left_imm, left_setup) = helpI left in
       let (right_imm, right_setup) = helpI right in
       (CPrim2(op, left_imm, right_imm, ()), left_setup @ right_setup)
    | EIf(cond, _then, _else, _) ->
       let (cond_imm, cond_setup) = helpI cond in
       (CIf(cond_imm, helpA _then, helpA _else, ()), cond_setup)
    | ELet([], body, _) -> helpC body
    | ELet((BBlank(_, _), exp, _)::rest, body, pos) ->
       let (exp_ans, exp_setup) = helpC exp in
       let (body_ans, body_setup) = helpC (ELet(rest, body, pos)) in
       (body_ans, exp_setup @ [BSeq(exp_ans)] @ body_setup)
    | ELet((BName(bind, _, _), exp, _)::rest, body, pos) ->
       let (exp_ans, exp_setup) = helpC exp in
       let (body_ans, body_setup) = helpC (ELet(rest, body, pos)) in
       (body_ans, exp_setup @ [BLet(bind, exp_ans)] @ body_setup)
    | ELet((BTuple(binds, _), exp, _)::rest, body, pos) ->
       raise (InternalCompilerError("Tuple bindings should have been desugared away"))
    | ESeq(e1, e2, _) ->
       let (e1_ans, e1_setup) = helpC e1 in
       let (e2_ans, e2_setup) = helpC e2 in
       (e2_ans, e1_setup @ [BSeq e1_ans] @ e2_setup)

    | EApp(funname, args, _) ->
       raise (NotYetImplemented("Revise this case"))
    | ETuple(args, _) ->
       raise (NotYetImplemented("Finish this case"))
    | EGetItem(tup, idx, len, _) ->
       raise (NotYetImplemented("Finish this case"))
    | ESetItem(tup, idx, len, newval, _) ->
       raise (NotYetImplemented("Finish this case"))
         
    | ELambda(binds, body, _) ->
       raise (NotYetImplemented("Finish this case"))
    | ELetRec(binds, body, _) ->
       raise (NotYetImplemented("Finish this case"))

    | _ -> let (imm, setup) = helpI e in (CImmExpr imm, setup)

  and helpI (e : tag expr) : (unit immexpr * unit anf_bind list) =
    match e with
    | ENumber(n, _) -> (ImmNum(n, ()), [])
    | EBool(b, _) -> (ImmBool(b, ()), [])
    | EId(name, _) -> (ImmId(name, ()), [])
    | ENil _ -> (ImmNil(), [])
    | EAnnot(e, _, _) -> helpI e

    | ESeq(e1, e2, _) ->
       let (e1_imm, e1_setup) = helpI e1 in
       let (e2_imm, e2_setup) = helpI e2 in
       (e2_imm, e1_setup @ e2_setup)


    | ETuple(args, tag) ->
       raise (NotYetImplemented("Finish this case"))
       (* Hint: use BLet to bind the result *)
    | EGetItem(tup, idx, len, tag) ->
       raise (NotYetImplemented("Finish this case"))
    | ESetItem(tup, idx, len, newval, tag) ->
       raise (NotYetImplemented("Finish this case"))

    | EPrim1(op, arg, tag) ->
       let tmp = sprintf "unary_%d" tag in
       let (arg_imm, arg_setup) = helpI arg in
       (ImmId(tmp, ()), arg_setup @ [BLet(tmp, CPrim1(op, arg_imm, ()))])
    | EPrim2(op, left, right, tag) ->
       let tmp = sprintf "binop_%d" tag in
       let (left_imm, left_setup) = helpI left in
       let (right_imm, right_setup) = helpI right in
       (ImmId(tmp, ()), left_setup @ right_setup @ [BLet(tmp, CPrim2(op, left_imm, right_imm, ()))])
    | EIf(cond, _then, _else, tag) ->
       let tmp = sprintf "if_%d" tag in
       let (cond_imm, cond_setup) = helpI cond in
       (ImmId(tmp, ()), cond_setup @ [BLet(tmp, CIf(cond_imm, helpA _then, helpA _else, ()))])
    | EApp(funname, args, tag) ->
       raise (NotYetImplemented("Revise this case"))
    | ELet([], body, _) -> helpI body
    | ELet((BBlank(_, _), exp, _)::rest, body, pos) ->
       let (exp_ans, exp_setup) = helpI exp in (* MUST BE helpI, to avoid any missing final steps *)
       let (body_ans, body_setup) = helpI (ELet(rest, body, pos)) in
       (body_ans, exp_setup @ body_setup)
    | ELambda(binds, body, tag) ->
       raise (NotYetImplemented("Finish this case"))
       (* Hint: use BLet to bind the answer *)
    | ELet((BName(bind, _, _), exp, _)::rest, body, pos) ->
       let (exp_ans, exp_setup) = helpC exp in
       let (body_ans, body_setup) = helpI (ELet(rest, body, pos)) in
       (body_ans, exp_setup @ [BLet(bind, exp_ans)] @ body_setup)
    | ELet((BTuple(binds, _), exp, _)::rest, body, pos) ->
       raise (InternalCompilerError("Tuple bindings should have been desugared away"))
    | ELetRec(binds, body, tag) ->
       raise (NotYetImplemented("Finish this case"))
       (* Hint: use BLetRec for each of the binds, and BLet for the final answer *)
  and helpA e : unit aexpr = 
    let (ans, ans_setup) = helpC e in
    List.fold_right
      (fun bind body ->
        (* Here's where the anf_bind datatype becomes most useful:
             BSeq binds get dropped, and turned into ASeq aexprs.
             BLet binds get wrapped back into ALet aexprs.
             BLetRec binds get wrapped back into ALetRec aexprs.
           Syntactically it looks like we're just replacing Bwhatever with Awhatever,
           but that's exactly the information needed to know which aexpr to build. *)
        match bind with
        | BSeq(exp) -> ASeq(exp, body, ())
        | BLet(name, exp) -> ALet(name, exp, body, ())
        | BLetRec(names) -> ALetRec(names, body, ()))
      ans_setup (ACExpr ans)
  in
  helpP p
;;


let is_well_formed (p : sourcespan program) : (sourcespan program) fallible =
  let rec wf_E (e : sourcespan expr) (* other parameters may be needed here *) =
    Error([NotYetImplemented "Implement well-formedness checking for expressions"])
  and wf_D (d : sourcespan decl) (* other parameters may be needed here *) =
    Error([NotYetImplemented "Implement well-formedness checking for definitions"])
  and wf_G (g : sourcespan decl list) (* other parameters may be needed here *) =
    Error([NotYetImplemented "Implement well-formedness checking for definition groups"])
  and wf_T (t : sourcespan typ) (* other parameters may be needed here *) =
    Error([NotYetImplemented "Implement well-formedness checking for types"])
  and wf_S (s : sourcespan scheme) (* other parameters may be needed here *) =
    Error([NotYetImplemented "Implement well-formedness checking for typeschemes"])
  and wf_TD (t : sourcespan tydecl) (* other parameters may be needed here *) =
    Error([NotYetImplemented "Implement well-formedness checking for type declarations"])
  in
  match p with
  | Program(tydecls, decls, body, _) ->
     Error([NotYetImplemented "Implement well-formedness checking for programs"])
;;


let desugar (p : sourcespan program) : sourcespan program =
  let gensym =
    let next = ref 0 in
    (fun name ->
      next := !next + 1;
      sprintf "%s_%d" name (!next)) in
  let rec helpE (e : sourcespan expr) (* other parameters may be needed here *) =
    Error([NotYetImplemented "Implement desugaring for expressions"])
  and helpD (d : sourcespan decl) (* other parameters may be needed here *) =
    Error([NotYetImplemented "Implement desugaring for definitions"])
  and helpG (g : sourcespan decl list) (* other parameters may be needed here *) =
    Error([NotYetImplemented "Implement desugaring for definition groups"])
  and helpT (t : sourcespan typ) (* other parameters may be needed here *) =
    Error([NotYetImplemented "Implement desugaring for types"])
  and helpS (s : sourcespan scheme) (* other parameters may be needed here *) =
    Error([NotYetImplemented "Implement desugaring for typeschemes"])
  and helpTD (t : sourcespan tydecl) (* other parameters may be needed here *) =
    Error([NotYetImplemented "Implement desugaring for type declarations"])
  in
  match p with
  | Program(tydecls, decls, body, _) ->
      raise (NotYetImplemented "Implement desugaring for programs")
;;



let rec compile_fun (fun_name : string) args body env : instruction list =
  raise (NotYetImplemented "Compile funs not yet implemented")
and compile_aexpr (e : tag aexpr) (si : int) (env : arg envt) (num_args : int) (is_tail : bool) : instruction list =
  raise (NotYetImplemented "Compile aexpr not yet implemented")
and compile_cexpr (e : tag cexpr) si env num_args is_tail =
  raise (NotYetImplemented "Compile cexpr not yet implemented")
and compile_imm e env =
  match e with
  | ImmNum(n, _) -> Const((n lsl 1))
  | ImmBool(true, _) -> const_true
  | ImmBool(false, _) -> const_false
  | ImmId(x, _) -> (find env x)
  | ImmNil(_) -> raise (NotYetImplemented "Finish this")

let compile_decl (d : tag adecl) : instruction list =
  raise (NotYetImplemented "Compile decl not yet implemented")

let compile_prog (anfed : tag aprogram) : string =
  match anfed with
  | AProgram(decls, body, _) ->
     let comp_decls = raise (NotYetImplemented "... do stuff with decls ...") in
     let (body_prologue, comp_body, body_epilogue) = raise (NotYetImplemented "... do stuff with body ...") in
     
     let heap_start = [
         ILineComment("heap start");
         IInstrComment(IMov(Reg(ESI), RegOffset(4, ESP)), "Load ESI with our argument, the heap pointer");
         IInstrComment(IAdd(Reg(ESI), Const(7)), "Align it to the nearest multiple of 8");
         IInstrComment(IAnd(Reg(ESI), HexConst(0xFFFFFFF8)), "by adding no more than 7 to it")
       ] in
     let main = to_asm (body_prologue @ heap_start @ comp_body @ body_epilogue) in
     
     raise (NotYetImplemented "... combine comp_decls and main with any needed extra setup and error handling ...")

let typecheck p =
  (* You should replace this with either type_synth or type_check *)
  Ok p
           
(* Feel free to add additional phases to your pipeline.
   The final pipeline phase needs to return a string,
   but everything else is up to you. *)

(* Add at least one desugaring phase somewhere in here, as well as your typechecker *)
(* You may want to desugar once before type-checking, and once afterward *)
let compile_to_string (prog : sourcespan program pipeline) : string pipeline =
  prog
  |> (add_err_phase well_formed is_well_formed)
  |> (if !skip_typechecking then no_op_phase else (add_err_phase type_checked typecheck))
  |> (add_phase tagged tag)
  |> (add_phase renamed rename_and_tag)
  |> (add_phase anfed (fun p -> atag (anf p)))
  |> (add_phase result compile_prog)
;;
