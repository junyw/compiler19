open Printf
open Exprs
open Assembly
open Errors
open Pretty
open Phases
open Inference

type 'a envt = (string * 'a) list
module StringSet = Set.Make(String);;
module StringMap = Map.Make(String);;

let skip_typechecking = ref false

let print_env env how =
  debug_printf "Env is\n";
  List.iter (fun (id, bind) -> debug_printf "  %s -> %s\n" id (how bind)) env;;


let find env (x : string) (loc : string) =
  let rec help ls =
    match ls with
    | [] -> raise (InternalCompilerError (sprintf "Name %s not found at %s" x loc))
    | (y,v)::rest ->
       if y = x then v else help rest
  in help env
;;

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
;;


let num_tag =          0x00000000
let num_tag_mask =     0x00000001
let bool_tag =         0x00000007
let bool_tag_mask =    0x00000007
let tuple_tag =        0x00000001
let tuple_tag_mask =   0x00000007
let closure_tag =      0x00000005
let closure_tag_mask = 0x00000007
let const_true =  HexConst(0xFFFFFFFF)
let const_false = HexConst(0x7FFFFFFF)
let bool_mask =   HexConst(0x80000000)
let const_nil =   HexConst(tuple_tag)

let err_COMP_NOT_NUM   = 1
let err_ARITH_NOT_NUM  = 2
let err_LOGIC_NOT_BOOL = 3
let err_IF_NOT_BOOL    = 4
let err_OVERFLOW       = 5
let err_GET_NOT_TUPLE  = 6
let err_GET_LOW_INDEX  = 7
let err_GET_HIGH_INDEX = 8
let err_NIL_DEREF      = 9
let err_OUT_OF_MEMORY    = 10
let err_SET_NOT_TUPLE    = 11
let err_SET_LOW_INDEX    = 12
let err_SET_HIGH_INDEX   = 13
let err_CALL_NOT_CLOSURE = 14
let err_CALL_ARITY_ERR   = 15


let initial_env : int envt = [] (* TODO *)
  (*raise (NotYetImplemented "Come up with an initial environment of global functions (names and arities)")*)
;;

(* FINISH THIS FUNCTION WITH THE WELL-FORMEDNESS FROM FER-DE-LANCE *)
let is_well_formed (p : sourcespan program) : (sourcespan program) fallible =
  let rec wf_E e (env : sourcespan envt) (tyenv : StringSet.t) =
    match e with
    | ESeq(e1, e2, _) -> wf_E e1 env tyenv @ wf_E e2 env tyenv
    | ETuple(es, _) -> List.concat (List.map (fun e -> wf_E e env tyenv) es)
    | EGetItem(e, idx, len, pos) ->
       (if idx >= len || len < 0 || idx < 0 then [Arity(len, idx, pos)] else [])
       @ wf_E e env tyenv
    | ESetItem(e, idx, len, newval, pos) ->
       (if idx >= len || len < 0 || idx < 0 then [Arity(len, idx, pos)] else [])
       @ wf_E e env tyenv @ wf_E newval env tyenv
    | EAnnot(e, t, _) -> wf_E e env tyenv @ wf_T tyenv t
    | ENil _ -> []
    | EBool _ -> []
    | ENumber(n, loc) ->
       if n > 1073741823 || n < -1073741824 then [Overflow(n, loc)] else []
    | EId (x, loc) ->
       (try ignore (List.assoc x env); []
        with Not_found -> [UnboundId(x, loc)])
    | EPrim1(_, e, _) -> wf_E e env tyenv
    | EPrim2(_, l, r, _) -> wf_E l env tyenv @ wf_E r env tyenv
    | EIf(c, t, f, _) -> wf_E c env tyenv @ wf_E t env tyenv @ wf_E f env tyenv
    | ELet(bindings, body, _) ->
       let rec find_locs x (binds : 'a bind list) : 'a list =
         match binds with
         | [] -> []
         | BBlank _::rest -> find_locs x rest
         | BName(y, _, loc)::rest ->
            if x = y then loc :: find_locs x rest
            else  find_locs x rest
         | BTuple(binds, _)::rest -> find_locs x binds @ find_locs x rest in
       let rec find_dupes (binds : 'a bind list) : exn list =
         match binds with
         | [] -> []
         | (BBlank _::rest) -> find_dupes rest
         | (BName(x, _, def)::rest) -> List.map (fun use -> DuplicateId(x, use, def)) (find_locs x rest)
         | (BTuple(binds, _)::rest) -> find_dupes (binds @ rest) in
       let dupeIds = find_dupes (List.map (fun (b, _, _) -> b) bindings) in
       let rec process_binds (rem_binds : 'a bind list) env =
         match rem_binds with
         | [] -> (env, [])
         | BBlank _::rest -> process_binds rest env
         | BTuple(binds, _)::rest -> process_binds (binds @ rest) env
         | BName(x, typ, xloc)::rest ->
            let shadow =
              try
                let existing = List.assoc x env in [ShadowId(x, xloc, existing)]
              with Not_found -> [] in
            let new_env = (x, xloc)::env in
            let (newer_env, errs) = process_binds rest new_env in
            (newer_env, (shadow @ errs)) in
       let rec process_bindings bindings env =
         match bindings with
         | [] -> (env, [])
         | (b, e, loc)::rest ->
            let (env, errs) = process_binds [b] env in
            let errs_e = wf_E e env tyenv in
            let (env', errs') = process_bindings rest env in
            (env', errs @ errs_e @ errs') in
       let (env2, errs) = process_bindings bindings env in
       dupeIds @ errs @ wf_E body env2 tyenv
    | ELetRec(binds, body, loc) -> [(* TODO *)] (* raise (NotYetImplemented "Finish well-formedness for ELetRec") *)
    | EApp(fn, args, loc) ->
       wf_E fn env tyenv @ List.concat (List.map (fun e -> wf_E e env tyenv) args)
    | ELambda(binds, body, loc) -> [(* TODO *)] (* raise (NotYetImplemented "Finish well-formedness for ELambda") *)
    | ENew _ | EDot _  | EDotSet _ -> [(* TODO *)]
  and wf_D d (env : sourcespan envt) (tyenv : StringSet.t) =
    match d with
    | DFun(fn, args, typ, body, loc) ->
       let rec dupe x args =
         match args with
         | [] -> None
         | BName(y, _, loc)::_ when x = y -> Some loc
         | BTuple(binds, _)::rest -> dupe x (binds @ rest)
         | _::rest -> dupe x rest in
       let rec process_args rem_args =
         match rem_args with
         | [] -> []
         | BBlank _::rest -> process_args rest
         | BName(x, _, loc)::rest ->
            (match dupe x rest with
             | None -> []
             | Some where -> [DuplicateId(x, where, loc)]) @ process_args rest
         | BTuple(binds, loc)::rest ->
            process_args (binds @ rest)
       in
       let rec arg_env args =
         match args with
         | [] -> []
         | BBlank _ :: rest -> arg_env rest
         | BName(name, _, loc)::rest -> (name, loc)::arg_env rest
         | BTuple(binds, _)::rest -> arg_env (binds @ rest) in
       (wf_S tyenv typ) @ (process_args args) @ (wf_E body ((fn, loc) :: arg_env args @ env) tyenv)
  and wf_G (g : sourcespan decl list) (env : sourcespan envt) (tyenv : StringSet.t) =
    List.concat (List.map (fun d -> wf_D d env tyenv) g)
  and wf_T (tyenv : StringSet.t) (t : sourcespan typ) =
    match t with
    | TyBlank _ -> []
    | TyCon(name, loc) -> if StringSet.mem name tyenv then [] else [UnboundTyId(name, loc)]
    | TyArr(args, ret, _) -> List.flatten (List.map (wf_T tyenv) (ret :: args))
    | TyApp(t, args, _) -> List.flatten (List.map (wf_T tyenv) (t :: args))
    | TyVar(name, loc) -> if StringSet.mem name tyenv then [] else [UnboundTyId(name, loc)]
    | TyTup(args, _) -> List.flatten (List.map (wf_T tyenv) args)
  and wf_S (tyenv : StringSet.t) (s : sourcespan scheme) =
    match s with
    | SForall(args, typ, _) ->
       wf_T (StringSet.union tyenv (StringSet.of_list args)) typ
  and wf_TD (t : sourcespan tydecl) (tyenv : StringSet.t) =
    match t with
    | TyDecl(name, args, _) ->
       let tyenv = StringSet.add name tyenv in
       let errs = List.flatten (List.map (wf_T tyenv) args) in
       (errs, tyenv)
  in
  match p with
  | Program(tydecls, classdecls(*TODO*), decls, body, _) ->
     let rec find name (decls : 'a decl list) =
       match decls with
       | [] -> None
       | DFun(n, args, _, _, loc)::rest when n = name -> Some(loc)
       | _::rest -> find name rest in
     let rec dupe_funbinds decls =
       match decls with
       | [] -> []
       | DFun(name, args, _, _, loc)::rest ->
          (match find name rest with
          | None -> []
          | Some where -> [DuplicateFun(name, where, loc)]) @ dupe_funbinds rest in
     let all_decls = List.flatten decls in
     let helpTD (exns, tyenv) td =
       let (td_exns, tyenv) = wf_TD td tyenv in
       (exns @ td_exns, tyenv) in
     let initial_tyenv = StringSet.of_list ["Int"; "Bool"] in
     let (tydecl_errs, initial_tyenv) = List.fold_left helpTD ([], initial_tyenv) tydecls in
     let help_G (env, exns) g =
       let g_exns = wf_G g env initial_tyenv in
       let funbinds = List.map (fun d -> match d with | DFun(name, args, _, _, loc) -> (name, loc)) g in
       (env @ funbinds, exns @ g_exns) in
     let (initial_env, exns) = List.fold_left help_G (List.map (fun (a, _) -> (a, dummy_span)) initial_env, dupe_funbinds all_decls) decls in
     let exns = tydecl_errs @ exns @ (wf_E body initial_env initial_tyenv)
     in match exns with
        | [] -> Ok p
        | _ -> Error exns
;;


let rename_and_tag (p : tag program) : tag program =
  let rec rename env p =
    match p with
    | Program(tydecls, classdecls, decls, body, tag) ->
       Program(tydecls, List.map (helpK env) classdecls,
               List.map (fun g -> List.map (helpD env) g) decls, helpE env body, tag)
  and helpK env c =
    match c with
    | Class(name, base, fields, methods, tag) ->
      Class(name, base, fields, List.map (helpD env) methods, tag)
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
    | EAnnot(e, t, tag) -> EAnnot(helpE env e, t, tag)
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
         EId(find env name (string_of_expr_with string_of_int e), tag)
       with exn -> e)
    | EApp(name, args, tag) -> EApp(helpE env name, List.map (helpE env) args, tag)
    | ELet(bindings, body, tag) ->
       let (bindings', env') = helpBG env bindings in
       let body' = helpE env' body in
       ELet(bindings', body', tag)
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
   | EDot(expr, id, tag) ->
       EDot(helpE env expr, id, tag)
   | EDotSet(expr, id, new_value, tag) ->
       EDotSet(helpE env expr, id, helpE env new_value, tag)
   | ENew(class_name, tag) ->
       ENew(class_name, tag)


  in (rename [] p)
;;


(* obj_lookup: convert object operations to offsets *)
let obj_lookup (p : 'a program) : 'a program =
  p
;;



let defn_to_letrec (p : 'a program) : 'a program =
  let rec wrap groups body tag =
    match groups with
    | [] -> body
    | group::rest -> wrap_group group (wrap rest body tag) tag
  and wrap_group decls body tag =
    let decl_to_binding d =
      match d with
      | DFun(name, args, scheme, body, tag) ->
         (BName(name, instantiate scheme, tag), ELambda(args, body, tag), tag) in
    ELetRec(List.map decl_to_binding decls, body, tag) in
  match p with
  | Program(tydecls, classdecls, declgroups, body, tag) ->
     Program(tydecls, classdecls, [], wrap declgroups body tag, tag)

let desugar_bindings (p : sourcespan program) : sourcespan program =
  let gensym =
    let next = ref 0 in
    (fun name ->
      next := !next + 1;
      sprintf "%s_%d" name (!next)) in
  let rec helpP (p : sourcespan program) =
    match p with
    | Program(tydecls, classdecls, decls, body, tag) -> Program(tydecls, List.map helpK classdecls, List.map helpG decls, helpE body, tag)
  and helpK c =
    match c with
    | Class(name, base, binds, decls, tag) -> Class(name, base, binds, List.map helpD decls, tag)
  and helpG g =
    List.map helpD g
  and helpD d =
    match d with
    | DFun(name, args, ret, body, tag) ->
       let helpArg a =
         match a with
         | BTuple(_, tag) ->
            let name = gensym "argtup" in
            let typ = bind_to_typ a in
            let newbind = BName(name, typ, tag) in
            (newbind, [(a, EId(name, tag), tag)])
         | _ -> (a, []) in
       let (newargs, argbinds) = List.split (List.map helpArg args) in
       let newbody = ELet(List.flatten argbinds, body, tag) in
       DFun(name, newargs, ret, helpE newbody, tag)
  and helpBE bind =
    let (b, e, btag) = bind in
    match b with
    | BTuple(binds, ttag) ->
       let typ = bind_to_typ b in
       (match e with
        | EId _ ->
           expandTuple binds ttag typ e
        | _ ->
           let newname = gensym "tup" in
           (BName(newname, typ, ttag), e, btag) :: expandTuple binds ttag typ (EId(newname, ttag)))
    | _ -> [bind]
  and expandTuple binds tag typ source : sourcespan binding list =
    let len = List.length binds in
    let helpB i b =
      match b with
      | BBlank _ -> []
      | BName(name, typ, btag) -> [(b, EGetItem(source, i, len, tag), btag)]
      | BTuple(binds, tag) ->
         let newname = gensym "tup" in
         let newexpr = EId(newname, tag) in
         let t = match typ with
           | TyTup(typs, _) -> (List.nth typs i)
           | _ -> TyBlank tag in
         (BName(newname, t, tag), EGetItem(source, i, len, tag), tag) :: expandTuple binds tag t newexpr in
    List.flatten (List.mapi helpB binds)
  and helpE e =
    match e with
    | ESeq(e1, e2, tag) -> ELet([(BBlank(TyBlank tag, tag), helpE e1, tag)], helpE e2, tag)
    | ETuple(exprs, tag) -> ETuple(List.map helpE exprs, tag)
    | EGetItem(e, idx, len, tag) -> EGetItem(helpE e, idx, len, tag)
    | ESetItem(e, idx, len, newval, tag) -> ESetItem(helpE e, idx, len, helpE newval, tag)
    | EId(x, tag) -> EId(x, tag)
    | ENumber(n, tag) -> ENumber(n, tag)
    | EBool(b, tag) -> EBool(b, tag)
    | ENil(t, tag) -> ENil(t, tag)
    | EAnnot(e, t, tag) -> EAnnot(helpE e, t, tag)
    | EPrim1(op, e, tag) ->
       EPrim1(op, helpE e, tag)
    | EPrim2(op, e1, e2, tag) ->
       EPrim2(op, helpE e1, helpE e2, tag)
    | ELet(binds, body, tag) ->
       let newbinds = (List.map helpBE binds) in
       List.fold_right (fun binds body -> ELet(binds, body, tag)) newbinds (helpE body)
    | ELetRec(binds, body, tag) ->
       let newbinds = (List.map helpBE binds) in
       ELetRec(List.flatten newbinds, helpE body, tag)
    | EIf(cond, thn, els, tag) ->
       EIf(helpE cond, helpE thn, helpE els, tag)
    | EApp(name, args, tag) ->
       EApp(helpE name, List.map helpE args, tag)
    | ELambda(args, body, tag) ->
       let helpArg a =
         match a with
         | BTuple(_, tag) ->
            let name = gensym "argtup" in
            let typ = bind_to_typ a in
            let newbind = BName(name, typ, tag) in
            (newbind, [(a, EId(name, tag), tag)])
         | _ -> (a, []) in
       let (newargs, argbinds) = List.split (List.map helpArg args) in
       let newbody = ELet(List.flatten argbinds, body, tag) in
       ELambda(newargs, helpE newbody, tag)
   | ENew _ -> e
   | EDot(expr, idx, tag) -> EDot(helpE expr, idx, tag)
   | EDotSet(expr, idx, newval, tag) -> EDotSet(helpE expr, idx, helpE newval, tag)
  in helpP p
;;


type 'a anf_bind =
  | BSeq of 'a cexpr
  | BLet of string * 'a cexpr
  | BLetRec of (string * 'a cexpr) list

let anf (p : tag program) : unit aprogram =
  let rec helpP (p : tag program) : unit aprogram =
    match p with
    | Program(_, classdecls, decls, body, _) ->
      AProgram(List.map helpClass classdecls, List.concat(List.map helpG decls), helpA body, ())
  and helpClass (cls : tag classdecl) : unit aclassdecl =
      match cls with
      | Class (name, basename, fields, methods, tag) ->
         let field_names = List.map (fun a ->
                        match a with
                        | BName(a, _, _) -> a
                        | _ -> raise (InternalCompilerError("Tuple bindings should have been desugared away"))) fields in
        let anfed_methods  = List.map helpD methods in
        AClass(name, basename, field_names, anfed_methods, ())
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
    | EApp(funname, args, _) ->
       let (fun_ans, fun_setup) = helpI funname in
       let (new_args, new_setup) = List.split (List.map helpI args) in
       (CApp(fun_ans, new_args, ()), fun_setup @ List.concat new_setup)

    | ESeq(e1, e2, _) ->
       let (e1_ans, e1_setup) = helpC e1 in
       let (e2_ans, e2_setup) = helpC e2 in
       (e2_ans, e1_setup @ [BSeq e1_ans] @ e2_setup)

    | ETuple(args, _) ->
       let (new_args, new_setup) = List.split (List.map helpI args) in
       (CTuple(new_args, ()), List.concat new_setup)
    | EGetItem(tup, idx, len, _) ->
       let (tup_imm, tup_setup) = helpI tup in
       (CGetItem(tup_imm, idx, ()), tup_setup)
    | ESetItem(tup, idx, len, newval, _) ->
       let (tup_imm, tup_setup) = helpI tup in
       let (new_imm, new_setup) = helpI newval in
       (CSetItem(tup_imm, idx, new_imm, ()), tup_setup @ new_setup)

    | ELambda(binds, body, _) ->
       let args = List.map (fun a ->
                      match a with
                      | BName(a, _, _) -> a
                      | BBlank(_, _) -> gensym "blank"
                      | BTuple _ -> raise (InternalCompilerError("Tuple bindings should have been desugared away")))
                    binds in
       (CLambda(args, helpA body, ()), [])
    | ELetRec(binds, body, _) ->
       let name_of b =
         match b with
         | BName(name, _, _) -> name
         | _ -> raise (InternalCompilerError "Other bindings should be desugared or rejected") in
       let (names, new_binds_setup) = List.split (List.map (fun (b, rhs, _) -> (name_of b, helpC rhs)) binds) in
       let (new_binds, new_setup) = List.split new_binds_setup in
       let (body_ans, body_setup) = helpC body in
       (body_ans, (BLetRec (List.combine names new_binds)) :: body_setup)
    |EDot(expr, id, tag) ->
      let (expr_imm, expr_setup) = helpI expr in
      (CDot(expr_imm, id, ()), expr_setup)
    |EDotSet(expr, id, new_val, tag) ->
      let (expr_imm, expr_setup) = helpI expr in
      let (new_imm, new_setup) = helpI new_val in
      (CDotSet(expr_imm, id, new_imm, ()), expr_setup @ new_setup)
    |ENew(class_name, tag) -> (CNew(class_name, ()), [])
    | _ -> let (imm, setup) = helpI e in (CImmExpr imm, setup)

  and helpI (e : tag expr) : (unit immexpr * unit anf_bind list) =
    match e with
    | ENumber(n, _) -> (ImmNum(n, ()), [])
    | EBool(b, _) -> (ImmBool(b, ()), [])
    | EId(name, _) -> (ImmId(name, ()), [])
    | ENil _ -> (ImmNil(), [])
    | EAnnot(e, _, _) -> helpI e
    | EDot(expr, id, tag) ->
      let tmp = sprintf "dot_%d" tag in
      let (expr_imm, expr_setup) = helpI expr in
      (ImmId(tmp, ()), expr_setup @ [BLet(tmp, CDot(expr_imm, id, ()))])
    | EDotSet(expr, id, new_val, tag) ->
      let tmp = sprintf "dotset_%d" tag in
      let (expr_imm, expr_setup) = helpI expr in
      let (new_imm, new_setup) = helpI new_val in
      (ImmId(tmp, ()), expr_setup @ new_setup @ [BLet(tmp, CDotSet(expr_imm, id, new_imm, ()))])
    | ENew(class_name, tag) ->
      let tmp = sprintf "new_%d" tag in
      (ImmId(tmp, ()), [BLet(tmp, CNew(class_name, ()))])
    | ESeq(e1, e2, _) ->
       let (e1_imm, e1_setup) = helpI e1 in
       let (e2_imm, e2_setup) = helpI e2 in
       (e2_imm, e1_setup @ e2_setup)
    | ETuple(args, tag) ->
       let tmp = sprintf "tup_%d" tag in
       let (new_args, new_setup) = List.split (List.map helpI args) in
       (ImmId(tmp, ()), (List.concat new_setup) @ [BLet(tmp, CTuple(new_args, ()))])
    | EGetItem(tup, idx, len, tag) ->
       let tmp = sprintf "get_%d" tag in
       let (tup_imm, tup_setup) = helpI tup in
       (ImmId(tmp, ()), tup_setup @ [BLet(tmp, CGetItem(tup_imm, idx, ()))])
    | ESetItem(tup, idx, len, newval, tag) ->
       let tmp = sprintf "set_%d" tag in
       let (tup_imm, tup_setup) = helpI tup in
       let (new_imm, new_setup) = helpI newval in
       (ImmId(tmp, ()), tup_setup @ new_setup @ [BLet(tmp, CSetItem(tup_imm, idx, new_imm,()))])

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
       let tmp = sprintf "app_%d" tag in
       let (fun_ans, fun_setup) = helpI funname in
       let (new_args, new_setup) = List.split (List.map helpI args) in
       (ImmId(tmp, ()), fun_setup @ (List.concat new_setup) @ [BLet(tmp, CApp(fun_ans, new_args, ()))])
    | ELet([], body, _) -> helpI body
    | ELet((BBlank(_, _), exp, _)::rest, body, pos) ->
       let (exp_ans, exp_setup) = helpI exp in (* MUST BE helpI, to avoid any missing final steps *)
       let (body_ans, body_setup) = helpI (ELet(rest, body, pos)) in
       (body_ans, exp_setup @ body_setup)
    | ELambda(binds, body, tag) ->
       let tmp = sprintf "lam_%d" tag in
       let args = List.map (fun a ->
                      match a with
                      | BName(a, _, _) -> a
                      | BBlank(_, _) -> gensym "blank"
                      | BTuple _ -> raise (InternalCompilerError("Tuple bindings should have been desugared away")))
                    binds in
       (ImmId(tmp, ()), [BLet(tmp, CLambda(args, helpA body, ()))])
    | ELet((BName(bind, _, _), exp, _)::rest, body, pos) ->
       let (exp_ans, exp_setup) = helpC exp in
       let (body_ans, body_setup) = helpI (ELet(rest, body, pos)) in
       (body_ans, exp_setup @ [BLet(bind, exp_ans)] @ body_setup)
    | ELet((BTuple(binds, _), exp, _)::rest, body, pos) ->
       raise (InternalCompilerError("Tuple bindings should have been desugared away"))
    | ELetRec(binds, body, tag) ->
       let tmp = sprintf "lam_%d" tag in
       let name_of b =
         match b with
         | BName(name, _, _) -> name
         | _ -> raise (InternalCompilerError "Other bindings should be desugared or rejected") in
       let (names, new_binds_setup) = List.split (List.map (fun (b, rhs, _) -> (name_of b, helpC rhs)) binds) in
       let (new_binds, new_setup) = List.split new_binds_setup in
       let (body_ans, body_setup) = helpC body in
       (ImmId(tmp, ()), (List.concat new_setup)
                        @ [BLetRec (List.combine names new_binds)]
                        @ body_setup
                        @ [BLet(tmp, body_ans)])

  and helpA e : unit aexpr =
    let (ans, ans_setup) = helpC e in
    List.fold_right
      (fun bind body ->
        match bind with
        | BSeq(exp) -> ASeq(exp, body, ())
        | BLet(name, exp) -> ALet(name, exp, body, ())
        | BLetRec(names) -> ALetRec(names, body, ()))
      ans_setup (ACExpr ans)
  in
  helpP p
;;


let free_vars_E (e : 'a aexpr) (rec_binds : string list) : string list =
  let rec helpA (bound : string list) (e : 'a aexpr) : string list =
    match e with
    | ASeq(e1, e2, _) -> helpC bound e1 @ helpA bound e2
    | ALet(name, binding, body, _) ->
     (helpC bound binding) (* all the free variables in the binding, plus *)
     (* all the free variables in the body, except the name itself *)
     @ (helpA (name :: bound) body)
    | ALetRec(bindings, body, _) ->
       let names = List.map fst bindings in
       let new_bound = (names @ bound) in
        (helpA new_bound body) @ List.flatten (List.map (fun binding -> helpC new_bound (snd binding)) bindings)
    | ACExpr c -> helpC bound c
  and helpC (bound : string list) (e : 'a cexpr) : string list =
    match e with
    | CLambda(args, body, _) ->
      helpA (args @ bound) body
    | CIf(cond, thn, els, _) ->
      helpI bound cond @ helpA bound thn @ helpA bound els
    | CPrim1(_, arg, _) -> helpI bound arg
    | CPrim2(_, left, right, _) -> helpI bound left @ helpI bound right
    | CApp(fn, args, _) ->
      (helpI bound fn) @ (List.flatten (List.map (fun arg -> helpI bound arg) args))
    | CTuple(vals, _) -> List.flatten (List.map (fun v -> helpI bound v) vals)
    | CGetItem(tup, _, _) -> helpI bound tup
    | CSetItem(tup, _, rhs, _) -> helpI bound tup @ helpI bound rhs
    | CImmExpr i -> helpI bound i
    | CDot(expr, idx, _) -> helpI bound expr
    | CDotSet(expr, idx, newval, _) -> helpI bound expr @ helpI bound newval
    | CNew(_, _) -> []
  and helpI (bound : string list) (e : 'a immexpr) : string list =
    match e with
    | ImmId(name, _) ->
      (* a name is free if it is not bound *)
      if List.mem name bound then [] else [name]
    | _ -> []
  in List.sort_uniq String.compare (helpA rec_binds e)
;;
let free_vars_P (p : 'a aprogram) rec_binds : string list =
  match p with
  | AProgram(_,_,body, _) -> free_vars_E body rec_binds (* TODO *)
;;



let rec free_typ_tyvars typ =
  match typ with
  | TyBlank _ -> []
  | TyCon _ -> []
  | TyVar(s, _) -> [s]
  | TyArr(args, ret, _) -> List.concat (List.map free_typ_tyvars (args @ [ret]))
  | TyApp(typ, args, _) -> List.concat (List.map free_typ_tyvars (args @ [typ]))
  | TyTup(args, _) -> List.concat (List.map free_typ_tyvars args)
and free_scheme_tyvars (args, typ) =
  List.fold_left ExtList.List.remove (List.sort_uniq String.compare (free_typ_tyvars typ)) args
;;






let reserve size tag =
  let ok = sprintf "$memcheck_%d" tag in
  [
    IMov(Reg(EAX), LabelContents("HEAP_END"));
    ISub(Reg(EAX), Const(size));
    ICmp(Reg(EAX), Reg(ESI));
    IJge(Label ok);
    IPush(Reg(ESP)); (* stack_top in C *)
    IPush(Reg(EBP)); (* first_frame in C *)
    IPush(Const(size)); (* bytes_needed in C *)
    IPush(Reg(ESI)); (* alloc_ptr in C *)
    ICall(Label("try_gc"));
    IAdd(Reg(ESP), Const(16)); (* clean up after call *)
    (* assume gc success if returning here, so EAX holds the new ESI value *)
    IMov(Reg(ESI), Reg(EAX));
    ILabel(ok);
  ]
;;
(* IMPLEMENT THIS FROM YOUR PREVIOUS ASSIGNMENT *)
(* Additionally, you are provided an initial environment of values that you may want to
   assume should take up the first few stack slots.  See the compiliation of Programs
   below for one way to use this ability... *)

let rec compile_imm (e : tag immexpr) env : arg =
  match e with
  | ImmNum(n, _)      -> Const(n lsl 1)
  | ImmBool(true, _)  -> const_true
  | ImmBool(false, _) -> const_false
  | ImmId(x, loc)       ->
      begin try
        find env x (string_of_int loc)
      with _ -> raise (InternalCompilerError (sprintf "compile_imm: Name %s not found" x))
      end
  | ImmNil _ -> HexConst(0x00000001) (* an invalid pointer tagged as tuple *)
;;

(* compile_fun:
  name: name of the function
  args: names of arguments
  body: expression of the function body
  initial_env:
  returns prologue, comp_main, epilogue
*)
let rec compile_fun
      (name : string)
      (args : string list)
      (body : 'a aexpr)
      env (* TODO: why are we not using this initial_env anywhere in the compilation of functions *)
    : (instruction list * instruction list * instruction list) =

  let num_args = List.length args in
  let n = count_vars body in
  let lambda_label = sprintf "%s" name in
  let lambda_label_end = sprintf "end_of_%s" name in

  (*1. Compute the free-variables of the function, and sort them alphabetically.*)
  let free = List.sort (fun x y -> String.compare x y) (free_vars_E body args) in
  let num_free_vars = List.length free in
  (*2. Update the environment:*)
  (* The closure itself is the first argument [EBP + 8], other arguments start from [EBP + 12] *)
  (* All the free variables are mapped to the first few local-variable slots*)
  (* The body must be compiled with a starting stack-index that accommodates those already-initialized local variable slots used for the free-variables*)

  (* unpack the closure variables *)
  let load_closure =
    [ IMov(Reg(ECX), RegOffset(word_size * 2, EBP));
      ISub(Reg(ECX), HexConst(0x5)) ]
  in
  let moveClosureVarToStack fv i =
    (* move the i^th variable to the i^th slot *)
    (* from the (i+3)^rd slot in the closure *)
    [ ILineComment(("unpack closure variable " ^ fv ^ " to stack"));
      IMov(Reg(EAX), RegOffset(12 + 4 * i, ECX));
      IMov(RegOffset(~-word_size * i - 4, EBP), Reg(EAX));
    ]
  in
  let load_closure_variables = List.concat (List.mapi (fun i fv -> moveClosureVarToStack fv (0 + i)) free) in
  (* save locations of args to env *)
  let (env', i) = List.fold_left
      (fun (env, i) arg ->
        let arg_reg = RegOffset((word_size * i), EBP) in
          ((arg, arg_reg)::env, i+1)
      ) ([], 3) args
  in
  (* save locations of closure variables to env *)
  let (env'', i) = List.fold_left
      (fun (env, i) arg ->
        let arg_reg = RegOffset(~-word_size * i - 4, EBP) in
          ((arg, arg_reg)::env, i+1)
      ) (env', 0) free
  in
  (*3. Compile the body in the new environment*)
  let compiled_body = compile_aexpr body (1 + num_free_vars) env'' num_args false in

  (*4. Produce compiled code that, after the stack management and before the body, reads the saved
       free-variables out of the closure (which is passed in as the first function parameter), and
       stores them in the reserved local variable slots.*)

  let prologue =
      [ IJmp(Label(lambda_label_end));
        ILabel(lambda_label)     ]
    (* Prologue *)
    @ [
        (* save (previous, caller's) EBP on stack *)
        IPush(Reg(EBP));
        (* make current ESP the new EBP *)
        IMov(Reg(EBP), Reg(ESP));
        (* "allocate space" for N local variables *)
        ISub(Reg(ESP), Const(word_size * n));
      ]
  in
  let comp_main =
      [ ILineComment("load the self argument")]
    @ load_closure
    @ load_closure_variables
    @ [ ILineComment(sprintf "----start of lambda body %s -----" lambda_label)]
    @ compiled_body
    @ [ ILineComment(sprintf "----end of lambda body %s -----" lambda_label)]
  in
  let epilogue =
      [
        (* restore value of ESP to that just before call *)
        IMov(Reg(ESP), Reg(EBP));
        (* now, value at [ESP] is caller's (saved) EBP
            so: restore caller's EBP from stack [ESP] *)
        IPop(Reg(EBP));
        (* return to caller *)
        IRet;
      ]
    @ [ ILabel(lambda_label_end) ]
  in
    (prologue, comp_main, epilogue)

and compile_aexpr (e : tag aexpr) (si : int) (env : arg envt) (num_args : int) (is_tail : bool) : instruction list =
  match e with
  | ALet(id, cexpr, aexpr, _) ->
     (* TODO: Wherever you are dealing with compound expressions you need to make sure *)
     (* TODO: that a call to new maps and object to its respective class *)

     let prelude = compile_cexpr cexpr (si + 1) env num_args false in
     (* id_reg: position of the binding in memory *)
     let id_reg = RegOffset(~-(word_size * si), EBP) in
     let body = compile_aexpr aexpr (si + 1) ((id, id_reg)::env) num_args is_tail in
     prelude
     @ [ IMov(id_reg, Reg(EAX)) ]
     @ body
  | ACExpr(cexpr) -> begin match cexpr with
                      | CApp _ | CIf _ -> compile_cexpr cexpr si env num_args is_tail
                      | _ -> compile_cexpr cexpr si env num_args false
                     end
  | ALetRec(str_cexprs, aexpr, _) ->
    let num_of_lambdas = List.length str_cexprs in
    (* decide where the lambda tuple would be placed on the heap, and
       put the lambda pointer to the stack *)
    let (instrs0, env', _, _) =
      List.fold_left
        (fun (instrs, env', i, heap_offset) (id, cexpr) ->
            let free_vars =
              match cexpr with
              | CLambda(args, e, _) -> free_vars_E e args
              | _ -> failwith "compile ALetRec error"
            in
            let num_free_vars = List.length free_vars in
            let padding =
              if ((3 + num_free_vars) mod 2 == 1) then 1 else 0
            in
            let tuple_size = word_size * (3 + num_free_vars + padding) in
            let id_reg = RegOffset(~-(word_size * (si + i)), EBP) in
              (
                instrs @ [ IMov(Reg(EAX), Reg(ESI));
                IAdd(Reg(EAX), Const(heap_offset));
                IAdd(Reg(EAX), HexConst(0x5));
                IMov(id_reg, Reg(EAX)); ]
               ,
              (id, id_reg)::env', i + 1, heap_offset + tuple_size))
        ([], env, 0, 0) str_cexprs
    in
    (* compile lambdas *)
    let (instrs, _) =
      List.fold_left
        (fun (instrs, i) (id, cexpr) ->
          let cexpr_instr = compile_cexpr cexpr (si + i) env' num_args false in
            ( instrs @ cexpr_instr
            , i + 1) )
        ([], 0) str_cexprs
    in
    let body = compile_aexpr aexpr (si + num_of_lambdas) env' num_args is_tail in
    instrs0 @ instrs @ body

  | ASeq(cexpr, aexpr, _) ->
    let cexpr_instr = compile_cexpr cexpr (si + 1) env num_args false in
    let aexpr_instr = compile_aexpr aexpr (si + 1) env num_args is_tail in
    cexpr_instr @ aexpr_instr



(* Adding cfmap that is a list of string list envt *)

(*
  cfmap = [ (foo, [x, y, z]), (baz, [a, b]), (boo, [a, b, c, d])]
  here boo extends baz and so it also contains a, b as the field names,
  in case of field overridding we, are going to do find_all on a key and then
  select the first from the right of the list.
*)
and compile_cexpr (e : tag cexpr) si env cfmap ocmap num_args is_tail =
  let get_object_fields class_name =
    try
      List.find (fun (key, values) -> String.equal key class_name) cfmap
    with _ -> raise (InternalCompilerError (sprintf "get_object_fields: Class %s not found" class_name))
  in
  let get_object_size class_name =
    List.length get_object_fields class_name
  in
  let class_of_obj obj_name =
    try
      List.find (fun (key, values) -> String.equal key obj_name) ocmap
    with _ -> raise (InternalCompilerError (sprintf "class_of_obj: Object %s not found" obj_name))
  in
  let get_field_index class_name field_name =
      let fields = get_object_fields class_name in
      (* TODO *)
      let index = -1 in
      (* Gets the rightmost index *)
      List.mapi (fun (i, fn) -> if (String.equal fn field_name) then index = i) fields
      if (index  == -1)
      then raise (InternalCompilerError (sprintf "get_field_index: Field %s not found" field_name)
      else index
  in
  let assert_num (e_reg : arg) (error : string) =
    [ ILineComment("assert_num");
      IMov(Reg(EAX), e_reg);
      ITest(Reg(EAX), HexConst(0x00000001));
      IJnz(Label(error));
    ]
  (* check the value in e_reg is boolean *)
  and assert_bool (e_reg : arg) (error : string) =
    [ ILineComment("assert_bool");
      IMov(Reg(EAX), e_reg);
      IMov(Reg(EDX), Reg(EAX));
      IXor(Reg(EDX), HexConst(0x7FFFFFFF));
      ITest(Reg(EDX), HexConst(0x7FFFFFFF));
      IJnz(Label(error));
    ]
  in
  match e with
  | CIf(immexpr, aexpr, aexpr2, tag) ->
    let else_label = sprintf "$if_false_%d" tag in
    let done_label = sprintf "$done_%d" tag in
        [ IMov(Reg(EAX), compile_imm immexpr env) ]
      @ assert_bool (Reg(EAX)) "err_if_not_bool"
      @ [ ICmp(Reg(EAX), const_false);
          IJe(Label(else_label)) ]
      @ compile_aexpr aexpr si env num_args is_tail
      @ [ IJmp(Label(done_label));
          ILabel(else_label) ]
      @ compile_aexpr aexpr2 si env num_args is_tail
      @ [ ILabel(done_label) ]
  | CPrim1(op, immexpr, tag) ->
     let e_reg = compile_imm immexpr env in
     let done_label = sprintf "$eprim1_done_%d" tag in
     begin match op with
     | Add1  ->
        assert_num e_reg "$err_arith_not_num" @
        [ IMov(Reg(EAX), e_reg);
          IAdd(Reg(EAX), Const(1 lsl 1));
          (* check overflow *)
          IJo(Label("$err_overflow"));
        ]
     | Sub1  ->
        assert_num e_reg "$err_arith_not_num" @
        [ IMov(Reg(EAX), e_reg);
          IAdd(Reg(EAX), Const(~-1 lsl 1));
          (* check overflow *)
          IJo(Label("$err_overflow"));
        ]
     | IsBool ->
        [ IMov(Reg(EAX), e_reg);
          IAnd(Reg(EAX), HexConst(0x7FFFFFFF));
          ICmp(Reg(EAX), HexConst(0x7FFFFFFF));
          IMov(Reg(EAX), const_true);
          IJe(Label(done_label));
          IMov(Reg(EAX), const_false);
          ILabel(done_label);
        ]
     | IsNum  ->
        [ IMov(Reg(EAX), e_reg);
          IAnd(Reg(EAX), HexConst(0x00000001));
          ICmp(Reg(EAX), HexConst(0));
          IMov(Reg(EAX), const_true);
          IJe(Label(done_label));
          IMov(Reg(EAX), const_false);
          ILabel(done_label);
        ];
     | IsTuple ->
        [ IMov(Reg(EAX), e_reg);
          IAnd(Reg(EAX), HexConst(0x00000111));
          ICmp(Reg(EAX), HexConst(0x00000001));
          IMov(Reg(EAX), const_true);
          IJe(Label(done_label));
          IMov(Reg(EAX), const_false);
          ILabel(done_label);
        ];
     | Not ->
        assert_bool e_reg "err_logic_not_bool"
        @ [ IMov(Reg(EAX), e_reg);
            IXor(Reg(EAX), Const(0x80000000));
          ]
     | PrintStack ->
        [ ILineComment("calling c function");
          IPush(Sized(DWORD_PTR, Const(num_args)));
          IPush(Sized(DWORD_PTR, Reg(EBP)));
          IPush(Sized(DWORD_PTR, Reg(ESP)));
          IPush(Sized(DWORD_PTR, e_reg));
          ICall(Label("print_stack"));
          IAdd(Reg(ESP), Const(word_size * 4));
        ]
     | Print ->
        [ ILineComment("calling c function");
          IPush(Sized(DWORD_PTR, e_reg));
          ICall(Label("print"));
          IAdd(Reg(ESP), Const(word_size * 1));
        ]
     | PrintB ->
        failwith "PrintB not implemented"
     end
  | CPrim2(op, imme1, imme2, tag) ->
     let e1_reg = compile_imm imme1 env in
     let e2_reg = compile_imm imme2 env in
     let done_label = sprintf "$eprim2_done_%d" tag in
     begin match op with
     | Plus  ->
        assert_num e1_reg "$err_arith_not_num" @
        assert_num e2_reg "$err_arith_not_num" @
        [ IMov(Reg(EAX), e1_reg);
          IAdd(Reg(EAX), e2_reg);
          (* check overflow *)
          IJo(Label("err_overflow"));
        ]
     | Minus ->
          assert_num e1_reg "$err_arith_not_num"
        @ assert_num e2_reg "$err_arith_not_num"
        @ [ IMov(Reg(EAX), e1_reg);
            ISub(Reg(EAX), e2_reg);
            (* check overflow *)
            IJo(Label("err_overflow"));
          ]
     | Times ->
          assert_num e1_reg "$err_arith_not_num"
        @ assert_num e2_reg "$err_arith_not_num"
        @ [ IMov(Reg(EAX), e1_reg);
            ISar(Reg(EAX), Const(1));
            IMul(Reg(EAX), e2_reg);
            (* check overflow *)
            IJo(Label("err_overflow"));
          ]
     | And   ->
          assert_bool e1_reg "err_logic_not_bool"
        @ assert_bool e2_reg "err_logic_not_bool"
        @ [ IMov(Reg(EAX), e1_reg);
            IAnd(Reg(EAX), e2_reg);
          ]
     | Or    ->
          assert_bool e1_reg "err_logic_not_bool"
        @ assert_bool e2_reg "err_logic_not_bool"
        @ [ IMov(Reg(EAX), e1_reg);
            IOr(Reg(EAX),  e2_reg);
          ]
     | Greater | GreaterEq | Less| LessEq ->
        let jump_instruction = match op with
        | Greater -> IJg(Label(done_label));
        | GreaterEq -> IJge(Label(done_label));
        | Less -> IJl(Label(done_label));
        | LessEq -> IJle(Label(done_label));
        | _ -> failwith "compile_cprim2_compare: not a compare operator"
        in
          assert_num e1_reg "err_comp_not_num"
        @ assert_num e2_reg "err_comp_not_num"
        @ [ IMov(Reg(EAX), e1_reg);
            ICmp(Reg(EAX), e2_reg);
            IMov(Reg(EAX), const_true);
          ]
        @ [ jump_instruction ]
        @ [ IMov(Reg(EAX), const_false);
            ILabel(done_label);
          ]
     | Eq   ->
        [ IMov(Reg(EAX), e1_reg);
          ICmp(Reg(EAX), e2_reg);
          IMov(Reg(EAX), const_true);
          IJe(Label(done_label));
          IMov(Reg(EAX), const_false);
          ILabel(done_label);
        ]
     | EqB -> failwith "compile_cexpr: EqB not implemented"
     end
  | CImmExpr(immexpr) -> [ IMov(Reg(EAX), compile_imm immexpr env) ]
  | CNew(class_name, tag) ->
    (*
        The header stores the number of elements in the Object. The value is not tagged.
        if the object in an instance of a class that extends another class then
        all the fields that corresponds to the base class with come before.
        In case of multilevel inheritance, the fields of the Root class will come
        first followed by fields of the base class
        (4 bytes) (4 bytes)  (4 bytes) (4 bytes)
    --------------------------------------------------------------
    | # elements | base_field_1 | base_field_2 | field_1 | field_2
    --------------------------------------------------------------
    *)

     let size = get_object_size class_name in
     if size == 0 then raise (
        InternalCompilerError (sprintf "CNew: Class Name %s not found" class_name)
     let gc_instr =
       [ (* call try_gc *)
         ILineComment("calling try_gc function");
         IPush(Sized(DWORD_PTR, Reg(ESP)));
         IPush(Sized(DWORD_PTR, Reg(EBP)));
         IPush(Sized(DWORD_PTR, Const(word_size * (size + 1))));
         IPush(Sized(DWORD_PTR, Reg(ESI)));
         ICall(Label("try_gc"));
         IAdd(Reg(ESP), Const(word_size * 4));
         (* try_gc returns the new heap top, store the value in ESI *)
         IMov(Reg(ESI), Reg(EAX));
       ]
     in

     (* store the size of the object *)
     let header_instr =
     (* Use the last bit of size to indicate whether it is forwarding *)
       [ IMov(RegOffset(0, ESI), Sized(DWORD_PTR, Const(size lsl 1))) ]
     in

      [ ILineComment(("creating Object of length " ^ (string_of_int size))) ]
      @ gc_instr
      @ header_instr
      (* save the position of the object to EAX *)
      @ [ IMov(Reg(EAX), Reg(ESI)) ]
      (* tag the object *)
      @ [ IAdd(Reg(EAX), HexConst(0x1))] (* TODO: Objects decriptors are tagged *)

  | CDot(ImmId(obj_name, loc) as immexpr, name, tag) ->
      (* TODO: Logic to add method calling in case the name
       is not field but a method on the class *)
      let e_reg = compile_imm immexpr env in
      let class_of_obj = get_class obj_name in
      let offset =  get_field_index class_of_obj in
      (* get the object *)
      [ IMov(Reg(EAX), e_reg) ]
      (* TODO: check that EAX is indeed a class *)
      (* untag it *)
      @ [ ISub(Reg(EAX), HexConst(0x1)) ]
      (* get the i-th field *)
      @ [ IMov(Reg(EAX), RegOffset((word_size * (offset+1)), EAX))]

  | CDotSet(ImmId(obj_name, loc) as immexpr, name, immexpr2, tag) ->
      (* Only fields are mutable *)
      (* name has to be a valid field of the class object *)
      let e_reg1 = compile_imm immexpr1 env in
      let e_reg2 = compile_imm immexpr2 env in
      let class_of_obj = get_class obj_name in
      let offset =  get_field_index class_of_obj in
      (* get the object *)
      [ IMov(Reg(EAX), e_reg1) ]
      (* TODO: check that EAX is indeed an object *)
      (* untag it *)
      @ [ ISub(Reg(EAX), HexConst(0x1)) ]
      (* get the new value *)
      @ [ IMov(Reg(ECX), e_reg2) ]
      (* mutate the object *)
      @ [ IMov(RegOffset((word_size * (offset+1)), EAX), Reg(ECX)) ]
      (* leave the object as the result *)
      @ [ IAdd(Reg(EAX), HexConst(0x1)) ]
  | CTuple(immexprs, tag) ->
  (*
    The header stores the number of elements in the tuple. The value is not tagged.

      (4 bytes)    (4 bytes)  (4 bytes)          (4 bytes)
  --------------------------------------------------------
  | # elements | element_0 | element_1 | ... | element_n |
  --------------------------------------------------------
  *)
      let size = List.length immexprs in

      (* call try_gc *)
      (* int* try_gc(int* alloc_ptr, int bytes_needed, int* cur_frame, int* cur_stack_top) *)
      let gc_instr =
        [ (* call try_gc *)
          ILineComment("calling try_gc function");
          IPush(Sized(DWORD_PTR, Reg(ESP)));
          IPush(Sized(DWORD_PTR, Reg(EBP)));
          IPush(Sized(DWORD_PTR, Const(word_size * (size + 1))));
          IPush(Sized(DWORD_PTR, Reg(ESI)));
          ICall(Label("try_gc"));
          IAdd(Reg(ESP), Const(word_size * 4));
          (* try_gc returns the new heap top, store the value in ESI *)
          IMov(Reg(ESI), Reg(EAX));
        ]
      in
      (* store the size of the tuple *)
      let header_instr =
      (* Use the last bit of size to indicate whether it is forwarding *)
        [ IMov(RegOffset(0, ESI), Sized(DWORD_PTR, Const(size lsl 1))) ]
      in
      (* the elements of the tuple are already evaluated,
         move the values to the heap *)
      let (_, mov_instr) = List.fold_left
        (fun (i, instrs) immexpr ->
          let e_reg = compile_imm immexpr env in

          (i + 1, instrs
                @ [ IMov(Reg(EAX), e_reg);
                    IMov(RegOffset((word_size * i), ESI), Reg(EAX)); ])
        ) (1, []) immexprs
      in
        [ ILineComment(("creating tuple of length " ^ (string_of_int size))) ]
      @ gc_instr
      @ header_instr
      @ mov_instr
      (* save the position of the tuple to EAX *)
      @ [ IMov(Reg(EAX), Reg(ESI)) ]
      (* tag the tuple *)
      @ [ IAdd(Reg(EAX), HexConst(0x1)) ]
      (* bump the heap pointer *) (* no longer needed with try_gc *)
      (* @ [ IAdd(Reg(ESI), Const(word_size * (size + 1))) ] *)
      (* realign the heap *)
      (* @ [ IAdd(Reg(ESI), Const(if ((size + 1) mod 2 == 1) then word_size else 0)) ] *)

  | CGetItem(immexpr, i, tag) ->
      let e_reg = compile_imm immexpr env in
      (* get the tuple *)
        [ IMov(Reg(EAX), e_reg) ]
      (* TODO: check that EAX is indeed a tuple *)
      (* untag it *)
      @ [ ISub(Reg(EAX), HexConst(0x1)) ]
      (* TODO: check the index is within range *)

      (* get the i-th item *)
      @ [ IMov(Reg(EAX), RegOffset((word_size * (i+1)), EAX))]

  | CSetItem(immexpr1, i, immexpr2, tag) ->
      let e_reg1 = compile_imm immexpr1 env in
      let e_reg2 = compile_imm immexpr2 env in
      (* get the tuple *)
        [ IMov(Reg(EAX), e_reg1) ]
      (* TODO: check that EAX is indeed a tuple *)
      (* untag it *)
      @ [ ISub(Reg(EAX), HexConst(0x1)) ]
      (* TODO: check the index is within range *)

      (* get the new value *)
      @ [ IMov(Reg(ECX), e_reg2) ]
      (* mutate the tuple *)
      @ [ IMov(RegOffset((word_size * (i+1)), EAX), Reg(ECX)) ]
      (* leave the tuple as the result *)
      @ [ IAdd(Reg(EAX), HexConst(0x1)) ]

  | CLambda(args, aexpr, tag) ->
    let num_of_args = List.length args in
    let f_name = sprintf "f_%d" tag in
    let free = free_vars_E aexpr args in
    let num_free_vars = List.length free in

    let (prologue, comp_main, epilogue) = compile_fun f_name args aexpr env in
    let f_code = prologue @ comp_main @ epilogue in

    let lambda_label = sprintf "%s" f_name in (* must be the same as in compile_fun *)

    (* Creat the closure in heap *)
    (* represented as a heap-allocated tuple:
      ------------------------------------------------------------------------
      | arity | code ptr | N | var_1 | var_2 | ... | var_N | (maybe padding) |
      ------------------------------------------------------------------------
    *)

    (* call try_gc *)
    (* int* try_gc(int* alloc_ptr, int bytes_needed, int* cur_frame, int* cur_stack_top) *)
    let gc_instr =
      [ (* call try_gc *)
        ILineComment("calling try_gc function");
        IPush(Sized(DWORD_PTR, Reg(ESP)));
        IPush(Sized(DWORD_PTR, Reg(EBP)));
        IPush(Sized(DWORD_PTR, Const(word_size * (3 + num_free_vars))));
        IPush(Sized(DWORD_PTR, Reg(ESI)));
        ICall(Label("try_gc"));
        IAdd(Reg(ESP), Const(word_size * 4));
        (* try_gc returns the new heap top, store the value in ESI *)
        IMov(Reg(ESI), Reg(EAX));
      ]
    in
    let moveClosureVarToHeap fv i =
      (* move the i^th variable to the i^th slot *)
      (* from the (i+3)^rd slot in the closure *)
      try [ ILineComment(("move closure variable " ^ fv ^ " to heap"));
            IMov(Reg(EAX), (find env fv "moveClosureVarToHeap"));
            IMov(RegOffset(12 + 4 * i, ESI), Reg(EAX));
          ]
      with _ -> raise (InternalCompilerError (sprintf "moveClosureVarToHeap: Name %s not found" fv))
    in
    let save_closure_variables = List.concat (List.mapi (fun i fv -> moveClosureVarToHeap fv i) free) in

    let closure_setup =
      [ ILineComment(sprintf "-----start of creating closure %s in heap-----" lambda_label ) ]
      (* gc *)
    @ gc_instr
      (* arity *)
    @ [ IMov(RegOffset((word_size * 0), ESI), Sized(DWORD_PTR, Const(num_of_args lsl 1))) ]
      (* code-pointer *)
    @ [ IMov(RegOffset((word_size * 1), ESI), Sized(DWORD_PTR, Label(lambda_label))) ]
      (* number of free variables *)
    @ [ IMov(RegOffset((word_size * 2), ESI), Sized(DWORD_PTR, Const(num_free_vars))) ]
      (* copy free variabels *)
    @ save_closure_variables
      (* creates the closure value *)
    @ [ ILineComment(sprintf "closure %s create at heap" lambda_label);
      (* save the position of the closure to EAX *)
        IMov(Reg(EAX), Reg(ESI));
      (* tag the closure *)
        IAdd(Reg(EAX), HexConst(0x5)); ]

      (* update the heap pointer, keeping 8-byte alignment *)
      (* bump the heap pointer *)
    (* @ [ IAdd(Reg(ESI), Const(word_size * (3 + num_free_vars))) ] *)
      (* realign the heap *)
    (* @ [ IAdd(Reg(ESI), Const(if ((3 + num_free_vars) mod 2 == 1) then word_size else 0)) ] *)

    @ [ ILineComment(sprintf "-----end of creating closure %s in heap-----" lambda_label ) ]

    in
      f_code @ closure_setup

  | CApp(immexpr, immexprs, tag) ->
      let imm_reg = compile_imm immexpr env in
      let num_args = List.length immexprs in
      let imm_regs = List.map (fun expr -> compile_imm expr env) immexprs in
      let push_args = List.fold_left
        (fun instrs imm_reg ->
          [ IPush(Sized(DWORD_PTR, imm_reg)) ] @ instrs)
        [] imm_regs
      in
      (*1. Retrieve the function value, and check that it’s tagged as a closure.*)
        (* load the function *)
        [ IMov(Reg(EAX), imm_reg) ]
      @ [ (* check-tag EAX, 0x5 *)]
        (* untag the value*)
      @ [ ISub(Reg(EAX), HexConst(0x5)) ]
        (* check the arity *)
      @ [ ]
      (*2. Push all the arguments..*)
      @ [ ILineComment("push the arguments")]
      @ push_args
      (*3. Push the closure itself.*)
      @ [ ILineComment("push the closure on to stack")]
      @ [ IPush(Sized(DWORD_PTR, imm_reg)) ]
      (*4. Call the code-label in the closure.*)
      @ [ ICall(RegOffset((word_size * 1), EAX)) ]
      (*5. Pop the arguments and the closure.*)
      @ [ IAdd(Reg(ESP), Const((num_args + 1) * word_size)) ]


      (* check if it is built-in function *)
  (*    let tmp =
        match find_opt built_in fun_name with
        | Some(arity) -> sprintf "%s" fun_name
        | None -> sprintf "$fun_dec_%s" fun_name
      in
      let imm_regs = List.map (fun expr -> compile_imm expr env) immexprs in
  *)    (* the label of the function declaration *)
  (*    let num_of_args = List.length immexprs in
      let push_args = List.fold_left
          (fun instrs imm_reg ->
            [ IPush(Sized(DWORD_PTR, imm_reg)) ] @ instrs)
          [] imm_regs
      in
        [ ILineComment(sprintf "calling %s(%s) of %d arguments" fun_name tmp num_of_args);
          ILineComment(sprintf "caller has %d arguments" num_args);
          ILineComment(("tail call: " ^ (string_of_bool is_tail)));
        ]
        @ push_args @
        [
          ICall(tmp);
          IAdd(Reg(ESP), Const(num_of_args * word_size));
        ]
  *)

  (* native_to_lambda:
      given a stack offset and a pair of function name and arity
      returns (name, slot, code)
   *)
 and native_to_lambda i (name, arity) =
    let f_name = sprintf "f_%s" name in
    let lambda_label = sprintf "%s" f_name in (* must be the same as in compile_fun *)

    (* Creat the closure in heap *)

    (* call try_gc *)
    (* int* try_gc(int* alloc_ptr, int bytes_needed, int* cur_frame, int* cur_stack_top) *)
    let gc_instr =
      [ (* call try_gc *)
        ILineComment("calling try_gc function");
        IPush(Sized(DWORD_PTR, Reg(ESP)));
        IPush(Sized(DWORD_PTR, Reg(EBP)));
        IPush(Sized(DWORD_PTR, Const(word_size * 2)));
        IPush(Sized(DWORD_PTR, Reg(ESI)));
        ICall(Label("try_gc"));
        IAdd(Reg(ESP), Const(word_size * 4));
        (* try_gc returns the new heap top, store the value in ESI *)
        IMov(Reg(ESI), Reg(EAX));
      ]
    in
    (* position of the lambda ptr on stack *)
    let slot = RegOffset((word_size * -i), ESP) in
    let closure_setup =
      [ ILineComment(sprintf "-----start of creating 'native_to_lambda' closure %s in heap-----" lambda_label ) ]
      (* gc *)
    @ gc_instr
      (* arity *)
    @ [ IMov(RegOffset((word_size * 0), ESI), Sized(DWORD_PTR, Const(arity lsl 1))) ]
      (* code-pointer *)
    @ [ IMov(RegOffset((word_size * 1), ESI), Sized(DWORD_PTR, Label(lambda_label))) ]
      (* number of free variables *)
    @ [ IMov(RegOffset((word_size * 2), ESI), Sized(DWORD_PTR, Const(0))) ]
      (* creates the closure value *)
    @ [ ILineComment(sprintf "closure %s create at heap" lambda_label);
      (* save the position of the closure to EAX *)
        IMov(Reg(EAX), Reg(ESI));
        IAdd(Reg(EAX), HexConst(0x5)); (* tag the closure *)
        IMov(slot, Reg(EAX)); (* Save the value onto the stack *)
      ]
  @ [ ILineComment(sprintf "-----end of creating 'native_to_lambda' closure %s in heap-----" lambda_label ) ]
  in
    (lambda_label, slot, closure_setup)

(*TODO: figure out what is this env that the function is expecting *)
and compile_class (c : tag aclassdecl) i env : arg * instruction list =
(*
  The header stores the number of elements in the tuple. The value is not tagged.

(4 bytes)    (4 bytes)      (4 bytes)  (4 bytes) (4 bytes)
--------------------------------------------------------
| # 5 | pointer_to_base | method_1 | method_2 | method_3 |
--------------------------------------------------------
*)
  match c with
  | AClass(class_name, base, field_names (* Ignoring field names for class compilation*), methods, tag) ->
    let comp_methods = List.fold_left
      (fun instr decl ->
          match decl with
            | ADFun(f_name, args, body, _) ->
              let (prologue, main, epilogue) = compile_fun f_name args body env in
              instr
              @ [ILineComment(sprintf "Method %s.%s" class_name f_name)]
              @ prologue @ main @ epilogue )
    []
    methods
    in

    let method_env = List.map (fun decl ->
         match decl with
          | ADFun(name, args, body, _) -> (name, List.length args))
    methods
    in

    (* method_lambdas is a list of (lambda_name, stack_slot_with_lambda_pointer, lambda_descriptor) *)
    let method_lambdas = List.mapi native_to_lambda method_env in

    (* method_env is a list of (lambda_name, stack_slot_with_lambda_pointer)*)
    let names_and_pointers = List.map (fun (name, slot, _) -> (name, slot)) method_lambdas in

    (* comp_lambdas is a list of lambda_descriptors *)
    let comp_lambdas = List.map (fun (_, _, code) -> code) method_lambdas in

    let size = List.length methods + 2 in

    (* compile the class descriptor *)
    (* call try_gc *)
    (* int* try_gc(int* alloc_ptr, int bytes_needed, int* cur_frame, int* cur_stack_top) *)
    let gc_instr =
      [ (* call try_gc *)
        ILineComment("calling try_gc function");
        IPush(Sized(DWORD_PTR, Reg(ESP)));
        IPush(Sized(DWORD_PTR, Reg(EBP)));
        IPush(Sized(DWORD_PTR, Const(word_size * size)));
        IPush(Sized(DWORD_PTR, Reg(ESI)));
        ICall(Label("try_gc"));
        IAdd(Reg(ESP), Const(word_size * 4));
        (* try_gc returns the new heap top, store the value in ESI *)
        IMov(Reg(ESI), Reg(EAX));
      ]
    in

    (* Add this class descriptor pointer to the given stack slot *)
    let slot = RegOffset((word_size * -i), ESP) in

    (* store the size of the class descriptor *)

    let header_instr =
    (* Use the last bit of size to indicate whether it is forwarding *)
      [ IMov(RegOffset(0, ESI), Sized(DWORD_PTR, Const(size lsl 1))) ]
    in

    (* move lambda pointer to class descriptor on heap *)
    let (_, mov_instr) = List.fold_left (fun (index, inst) (lambda_name, lambda_pointer) ->
        let instr_for_method =
          [ILineComment("Adding %s lambda pointer for % class");
          IMov(RegOffset((word_size * index), ESI), lambda_pointer)]
        in
        (index + 1, inst @ instr_for_method))
    (2, [])
    names_and_pointers
    in

    let class_instr =
      [ ILineComment(sprintf "Methods of class %s" (string_of_aclassdecl c))]
      @ comp_methods
      [ ILineComment(sprintf "Lambdas of methods of class %s" (string_of_aclassdecl c))]
      @ comp_lambdas
      [ ILineComment(sprintf "creating class descriptor  %s" ^ (string_of_aclassdecl c)) ]
      @ gc_instr
      @ header_instr
      @ mov_instr
      (* save the position of the class descriptor to the stack *)
      @ [
          IMov(Reg(EAX), Reg(ESI));
          IAdd(Reg(EAX), HexConst(0x1)); (* tag the class descriptor *)
          IMov(slot, Reg(EAX))
        ]
    in
    (slot, class_instr)
;;


let native_call (label : arg) args =
  let setup = List.rev_map (fun arg ->
                  match arg with
                  | Sized _ -> IPush(arg)
                  | _ -> IPush(Sized(DWORD_PTR, arg))) args in
  let teardown =
    let len = List.length args in
    if len = 0 then []
    else [ IInstrComment(IAdd(Reg(ESP), Const(word_size * len)), sprintf "Popping %d arguments" len) ] in
  setup @ [ ICall(label) ] @ teardown
;;

(* UPDATE THIS TO HANDLE FIRST-CLASS FUNCTIONS AS NEEDED *)
let call (label : arg) args =
  let setup = List.rev_map (fun arg ->
                  match arg with
                  | Sized _ -> IPush(arg)
                  | _ -> IPush(Sized(DWORD_PTR, arg))) args in
  let teardown =
    let len = List.length args in
    if len = 0 then []
    else [ IInstrComment(IAdd(Reg(ESP), Const(4 * len)), sprintf "Popping %d arguments" len) ] in
  setup @ [ ICall(label) ] @ teardown
;;



let compile_prog anfed =
  let prelude =
    "section .text
extern error
extern print
extern print_stack
extern equal
extern try_gc
extern naive_print_heap
extern HEAP
extern HEAP_END
extern STACK_BOTTOM
global our_code_starts_here" in
  let suffix = sprintf "
err_comp_not_num:%s
err_arith_not_num:%s
err_logic_not_bool:%s
err_if_not_bool:%s
err_overflow:%s
err_get_not_tuple:%s
err_get_low_index:%s
err_get_high_index:%s
err_out_of_memory:%s
err_set_not_tuple:%s
err_set_low_index:%s
err_set_high_index:%s
err_call_not_closure:%s
err_call_arity_err:%s
err_nil_deref:%s
"
                       (to_asm (native_call (Label "error") [Const(err_COMP_NOT_NUM); Reg EAX]))
                       (to_asm (native_call (Label "error") [Const(err_ARITH_NOT_NUM); Reg EAX]))
                       (to_asm (native_call (Label "error") [Const(err_LOGIC_NOT_BOOL); Reg EAX]))
                       (to_asm (native_call (Label "error") [Const(err_IF_NOT_BOOL); Reg EAX]))
                       (to_asm (native_call (Label "error") [Const(err_OVERFLOW); Reg EAX]))
                       (to_asm (native_call (Label "error") [Const(err_GET_NOT_TUPLE); Reg EAX]))
                       (to_asm (native_call (Label "error") [Const(err_GET_LOW_INDEX); Reg EAX]))
                       (to_asm (native_call (Label "error") [Const(err_GET_HIGH_INDEX); Reg EAX]))
                       (to_asm (native_call (Label "error") [Const(err_OUT_OF_MEMORY); Reg EAX]))
                       (to_asm (native_call (Label "error") [Const(err_SET_NOT_TUPLE); Reg EAX]))
                       (to_asm (native_call (Label "error") [Const(err_SET_LOW_INDEX); Reg EAX]))
                       (to_asm (native_call (Label "error") [Const(err_SET_HIGH_INDEX); Reg EAX]))
                       (to_asm (native_call (Label "error") [Const(err_CALL_NOT_CLOSURE); Reg EAX]))
                       (to_asm (native_call (Label "error") [Const(err_CALL_ARITY_ERR); Reg EAX]))
                       (to_asm (native_call (Label "error") [Const(err_NIL_DEREF); Reg EAX]))
  in
  match anfed with
  | AProgram(classdecls, decls, body, _) ->
     let native_lambdas = List.mapi native_to_lambda initial_env in

     let initial_env = List.map (fun (name, slot, _) -> (name, slot)) native_lambdas in

     let comp_decls = List.map (fun (_, _, code) -> code) native_lambdas in
     (* Made changes here to include the initial environment in the class declaration *)
     let comp_classdecls = List.fold (fun (env, inst) classdecl ->
               compile_class classdecls 0 env in
     )

     List.map compile_class classdecls 0 initial_env in
  (* $heap is a mock parameter name, just so that compile_fun knows our_code_starts_here takes in 1 parameter *)

     let (prologue, comp_main, epilogue) = compile_fun "our_code_starts_here" ["$heap"] body initial_env in
     let heap_start = [
        (* Set the global variable STACK_BOTTOM to EBP *)
        IInstrComment(IMov(LabelContents("STACK_BOTTOM"), Reg(EBP)), "This is the bottom of our Garter stack");
        ILineComment("heap start");
        (* Store the HEAP to ESI, and ensure that it is a multiple of 8 *)
        (* Load ESI with the pass-in pointer *)
        IInstrComment(IMov(Reg(ESI), RegOffset((word_size * 2), EBP)), "Load ESI with our argument, the heap pointer");
        (* Add 7 to get above the next multiple of 8 *)
        IInstrComment(IAdd(Reg(ESI), Const(7)), "Align it to the nearest multiple of 8");
        (* Then round back down *)
        IInstrComment(IAnd(Reg(ESI), HexConst(0xFFFFFFF8)), "by adding no more than 7 to it")
       ] in
     let main = (prologue
       @ heap_start
       @ List.flatten comp_classdecls
       @ List.flatten comp_decls
       @ comp_main
       @ epilogue)
     in
     sprintf "%s%s%s\n" prelude (to_asm main) suffix


;;

let compile_to_string (prog : sourcespan program pipeline) : string pipeline =
  prog
  |> (add_err_phase well_formed is_well_formed)
  |> (add_phase desugared_bindings desugar_bindings)
  |> (if !skip_typechecking then no_op_phase else (add_err_phase type_checked type_synth))
  |> (add_phase desugared_objects obj_lookup)
  |> (add_phase tagged tag)
  |> (add_phase renamed rename_and_tag)
  |> (add_phase desugared_decls defn_to_letrec)
  |> (add_phase anfed (fun p -> (atag (anf p))))
  |>  debug
  |> (add_phase result compile_prog)
;;
