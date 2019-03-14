open Printf
open Pretty
open Phases
open Exprs
open Assembly
open Errors
open Inference 
       
type 'a envt = (string * 'a) list

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

let err_ARITH_NOT_NUM      = 1
let err_COMPARISON_NOT_NUM = 2
let err_IF_NOT_BOOL        = 3
let err_LOGIC_NOT_BOOL     = 4
let err_ARITH_OVERFLOW     = 5


(* You may find some of these helpers useful *)
let rec find ls x =
  match ls with
  | [] -> raise (InternalCompilerError (sprintf "Name %s not found" x))
  | (y,v)::rest ->
     if y = x then v else find rest x

let count_vars e =
  let rec helpA e =
    match e with
    | ALet(_, bind, body, _) -> 1 + (max (helpC bind) (helpA body))
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
  in (rename [] p)
;;


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
                      | _ -> raise (NotYetImplemented("helpD: Finish this"))) args in
       ADFun(name, args, helpA body, ())
  and helpC (e : tag expr) : (unit cexpr * (string * unit cexpr) list) = 
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
    | ELet((bind, expr, _)::rest, body, pos) -> 
        begin match bind with 
        | BBlank(typ, _) -> failwith "helpC: BBlank not implemented"
        | BTuple(binds, _) -> failwith "helpC: BTuple not implemented"
        | BName(id, typ, _) ->
          let (exp_ans, exp_setup) = helpC expr in
          let (body_ans, body_setup) = helpC (ELet(rest, body, pos)) in
          (body_ans, exp_setup @ [(id, exp_ans)] @ body_setup)
        end
    | EApp(funname, args, _) ->
       let (new_args, new_setup) = List.split (List.map helpI args) in
       (CApp(funname, new_args, ()), List.concat new_setup)
    | ETuple(exprs, _) -> 
       let (exprs_imm, exprs_setup) = List.split (List.map helpI exprs) in
       (CTuple(exprs_imm, ()),  List.concat exprs_setup)
    | EGetItem(expr, a, b, _) -> 
        let (expr_imm, expr_setup) = helpI expr in
        (CGetItem(expr_imm, a, ()), expr_setup)
    | ESetItem(expr1, a, b, expr2, _) -> 
        let (expr1_imm, expr1_setup) = helpI expr1 in
        let (expr2_imm, expr2_setup) = helpI expr2 in
        (CSetItem(expr1_imm, a, expr2_imm, ()), expr1_setup @ expr2_setup)

    (* NOTE: You may need more cases here, for sequences and tuples *)
    | _ -> let (imm, setup) = helpI e in (CImmExpr imm, setup)

  and helpI (e : tag expr) : (unit immexpr * (string * unit cexpr) list) =
    match e with
    | ENumber(n, _) -> (ImmNum(n, ()), [])
    | EBool(b, _) -> (ImmBool(b, ()), [])
    | EId(name, _) -> (ImmId(name, ()), [])
    | EAnnot(e, _, _) -> helpI e

    | EPrim1(op, arg, tag) ->
       let tmp = sprintf "unary_%d" tag in
       let (arg_imm, arg_setup) = helpI arg in
       (ImmId(tmp, ()), arg_setup @ [(tmp, CPrim1(op, arg_imm, ()))])
    | EPrim2(op, left, right, tag) ->
       let tmp = sprintf "binop_%d" tag in
       let (left_imm, left_setup) = helpI left in
       let (right_imm, right_setup) = helpI right in
       (ImmId(tmp, ()), left_setup @ right_setup @ [(tmp, CPrim2(op, left_imm, right_imm, ()))])
    | EIf(cond, _then, _else, tag) ->
       let tmp = sprintf "if_%d" tag in
       let (cond_imm, cond_setup) = helpI cond in
       (ImmId(tmp, ()), cond_setup @ [(tmp, CIf(cond_imm, helpA _then, helpA _else, ()))])
    | EApp(funname, args, tag) ->
       let tmp = sprintf "app_%d" tag in
       let (new_args, new_setup) = List.split (List.map helpI args) in
       (ImmId(tmp, ()), (List.concat new_setup) @ [(tmp, CApp(funname, new_args, ()))])
    | ELet([], body, _) -> helpI body
    | ELet((bind, expr, _)::rest, body, pos) ->
        begin match bind with 
        | BBlank(typ, _) -> failwith "helpI: BBlank not implemented"
        | BTuple(binds, _) -> failwith "helpI: BTuple not implemented"
        | BName(id, typ, _) ->
          let (exp_ans, exp_setup) = helpC expr in
          let (body_ans, body_setup) = helpI (ELet(rest, body, pos)) in
          (body_ans, exp_setup @ [(id, exp_ans)] @ body_setup)
        end
    | ETuple(exprs, tag) -> 
        let tmp = sprintf "tuple_%d" tag in
        let (exprs_imm, exprs_setup) = List.split (List.map helpI exprs) in
        (ImmId(tmp, ()), (List.concat exprs_setup) @ [(tmp, CTuple(exprs_imm, ()))])
    | EGetItem(expr, a, b, _) -> failwith "helpI: EGetItem not implemented"
    | ESetItem(expr, a, b, expr2, _) -> failwith "helpI: ESetItem not implemented"

    | _ -> raise (NotYetImplemented "Finish the remaining cases")
  and helpA e : unit aexpr = 
    let (ans, ans_setup) = helpC e in
    List.fold_right (fun (bind, exp) body -> ALet(bind, exp, body, ())) ans_setup (ACExpr ans)
  in
  helpP p


let is_well_formed (p : sourcespan program) : (sourcespan program) fallible =
  match p with
  | Program(tydecls, decls, body, _) -> Ok(p) (* TODO *)
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
      p (* TODO: implement me *)
;;


let rec compile_aexpr (e : tag aexpr) (si : int) (env : arg envt) (num_args : int) (is_tail : bool) : instruction list =
  match e with
  | ALet(id, cexpr, aexpr, _) -> 
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

and compile_cexpr (e : tag cexpr) si env num_args is_tail =
  let assert_num (e_reg : arg) (error : string) = 
    [ ILineComment("assert_num");
      IMov(Reg(EAX), e_reg);
      ITest(Reg(EAX), HexConst(0x00000001));
      IJnz(error);
    ]
  (* check the value in e_reg is boolean *)
  and assert_bool (e_reg : arg) (error : string) = 
    [ ILineComment("assert_bool");
      IMov(Reg(EAX), e_reg); 
      IMov(Reg(EDX), Reg(EAX));
      IXor(Reg(EDX), HexConst(0x7FFFFFFF));
      ITest(Reg(EDX), HexConst(0x7FFFFFFF));
      IJnz(error);
    ]
  in
  match e with 
  | CIf(immexpr, aexpr, aexpr2, tag) -> 
    let else_label = sprintf "$if_false_%d" tag in
    let done_label = sprintf "$done_%d" tag in
        [ IMov(Reg(EAX), compile_imm immexpr env) ]
      @ assert_bool (Reg(EAX)) "$err_if_not_boolean"
      @ [ ICmp(Reg(EAX), const_false); 
          IJe(else_label) ]
      @ compile_aexpr aexpr si env num_args is_tail
      @ [ IJmp(done_label); 
          ILabel(else_label) ]
      @ compile_aexpr aexpr2 si env num_args is_tail
      @ [ ILabel(done_label) ]
  | CPrim1(op, immexpr, tag) -> 
     let e_reg = compile_imm immexpr env in
     let done_label = sprintf "$eprim1_done_%d" tag in
     begin match op with
     | Add1  -> assert_num e_reg "$err_arith_not_num" @
                [ IMov(Reg(EAX), e_reg);
                  IAdd(Reg(EAX), Const(1 lsl 1)); 
                  (* check overflow *) 
                  IJo("$err_arith_overflow");
                ] 
     | Sub1  -> assert_num e_reg "$err_arith_not_num" @
                [ IMov(Reg(EAX), e_reg); 
                  IAdd(Reg(EAX), Const(~-1 lsl 1));
                  (* check overflow *) 
                  IJo("$err_arith_overflow");
                ] 
     | Print -> [ ILineComment("calling c function");
                  IPush(Sized(DWORD_PTR, e_reg)); 
                  ICall("print");
                  IAdd(Reg(ESP), Const(1*4));
                ]
     | PrintB -> failwith "compile_cexpr: PrintB not implemented"
     | IsBool -> 
        [ IMov(Reg(EAX), e_reg); 
          IAnd(Reg(EAX), HexConst(0x7FFFFFFF));
          ICmp(Reg(EAX), HexConst(0x7FFFFFFF));
          IMov(Reg(EAX), const_true);
          IJe(done_label);
          IMov(Reg(EAX), const_false);
          ILabel(done_label);
        ]
     | IsNum  -> 
        [ IMov(Reg(EAX), e_reg); 
          IAnd(Reg(EAX), HexConst(0x00000001));  
          ICmp(Reg(EAX), HexConst(0));
          IMov(Reg(EAX), const_true);
          IJe(done_label);
          IMov(Reg(EAX), const_false);
          ILabel(done_label);
        ];
     | IsTuple -> 
        [ IMov(Reg(EAX), e_reg); 
          IAnd(Reg(EAX), HexConst(0x00000111));
          ICmp(Reg(EAX), HexConst(0x00000111));
          IMov(Reg(EAX), const_true);
          IJe(done_label);
          IMov(Reg(EAX), const_false);
          ILabel(done_label);
        ];
     | Not ->
          assert_bool e_reg "$err_logic_not_boolean" 
        @ [ IMov(Reg(EAX), e_reg);
            IXor(Reg(EAX), Const(0x80000000));
          ]

     | PrintStack -> 
        [ ILineComment("calling c function");
          IPush(Sized(DWORD_PTR, Reg(ESP))); 
          IPush(Sized(DWORD_PTR, Reg(EBP)));
          IPush(Sized(DWORD_PTR, e_reg)); 
          ICall("printstack");
          IAdd(Reg(ESP), Const(3*4));
        ]
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
          IJo("err_arith_overflow");

        ]
     | Minus -> 
          assert_num e1_reg "$err_arith_not_num"
        @ assert_num e2_reg "$err_arith_not_num"
        @ [ IMov(Reg(EAX), e1_reg); 
            ISub(Reg(EAX), e2_reg);
            (* check overflow *) 
            IJo("err_arith_overflow");
          ]
     | Times -> 
          assert_num e1_reg "$err_arith_not_num"
        @ assert_num e2_reg "$err_arith_not_num"
        @ [ IMov(Reg(EAX), e1_reg); 
            ISar(Reg(EAX), Const(1));
            IMul(Reg(EAX), e2_reg);
            (* check overflow *) 
            IJo("err_arith_overflow");
          ]
     | And   -> 
          assert_bool e1_reg "$err_logic_not_boolean" 
        @ assert_bool e2_reg "$err_logic_not_boolean" 
        @ [ IMov(Reg(EAX), e1_reg); 
            IAnd(Reg(EAX), e2_reg); 
          ]
     | Or    -> 
          assert_bool e1_reg "$err_logic_not_boolean" 
        @ assert_bool e2_reg "$err_logic_not_boolean" 
        @ [ IMov(Reg(EAX), e1_reg); 
            IOr(Reg(EAX),  e2_reg);
          ]
     | Greater | GreaterEq | Less| LessEq ->
        let jump_instruction = match op with 
        | Greater -> IJg(done_label);
        | GreaterEq -> IJge(done_label);
        | Less -> IJl(done_label);
        | LessEq -> IJle(done_label);
        | _ -> failwith "compile_cprim2_compare: not a compare operator"
        in
          assert_num e1_reg "$err_comparison_not_num"
        @ assert_num e2_reg "$err_comparison_not_num"
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
          IJe(done_label);
          IMov(Reg(EAX), const_false);
          ILabel(done_label);
        ]
     | EqB -> failwith "compile_cexpr: EqB not implemented"
     end
  | CApp(fun_name, immexprs, tag) ->
    let imm_regs = List.map (fun expr -> compile_imm expr env) immexprs in
    (* the label of the function declaration *)
    let tmp = sprintf "$fun_dec_%s" fun_name in
    let tmp_body = sprintf "$fun_dec_body_%s" fun_name in
    let num_of_args = List.length immexprs in
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
  | CImmExpr(immexpr) -> [ IMov(Reg(EAX), compile_imm immexpr env) ]
  | CTuple(immexprs, tag) -> 
(*
  The header stores the number of elements in the tuple. The value is not tagged.

    (4 bytes)    (4 bytes)  (4 bytes)          (4 bytes)
--------------------------------------------------------
| # elements | element_0 | element_1 | ... | element_n |
--------------------------------------------------------
*)
      let size = List.length immexprs in
      (* store the size of the tuple *)
      let header_instr = 
        [ IMov(RegOffset(0, ESI), Sized(DWORD_PTR, Const(size))) ]
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
      @ header_instr
      @ mov_instr
      (* save the position of the tuple to EAX *)
      @ [ IMov(Reg(EAX), Reg(ESI)) ]
      (* tag the tuple *)
      @ [ IAdd(Reg(EAX), HexConst(0x111)) ]
      (* bump the heap pointer *)
      @ [ IAdd(Reg(ESI), Const(word_size * (size + 1))) ]
      (* realign the heap *)
      @ [ IAdd(Reg(ESI), Const(if ((size + 1) mod 2 == 1) then word_size else 0)) ]

  | CGetItem(immexpr, i, tag) -> 
      let e_reg = compile_imm immexpr env in
      (* get the tuple *)
        [ IMov(Reg(EAX), e_reg) ]
      (* TODO: check that EAX is indeed a tuple *)
      (* untag it *)
      @ [ ISub(Reg(EAX), HexConst(0x111)) ]
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
      @ [ ISub(Reg(EAX), HexConst(0x111)) ]
      (* TODO: check the index is within range *)

      (* get the new value *)
      @ [ IMov(Reg(ECX), e_reg2) ]
      (* mutate the tuple *)
      @ [ IMov(RegOffset((word_size * (i+1)), EAX), Reg(ECX)) ]
      (* leave the tuple as the result *)
      @ [ IAdd(Reg(EAX), HexConst(0x111)) ]


and compile_imm e env : arg =
  match e with
  | ImmNum(n, _)      -> Const(n lsl 1)
  | ImmBool(true, _)  -> const_true
  | ImmBool(false, _) -> const_false
  | ImmId(x, _)       -> (find env x)

and compile_decl (d : tag adecl) : instruction list =
  match d with 
  | ADFun(fun_name, args, aexpr, tag) ->
    let tmp = sprintf "$fun_dec_%s" fun_name in
    let tmp_body = sprintf "$fun_dec_body_%s" fun_name in
    let num_args = List.length args in
    let n = (count_vars aexpr) in
    let prelude = [
      (* save (previous, caller's) EBP on stack *)
      IPush(Reg(EBP));
      (* make current ESP the new EBP *)
      IMov(Reg(EBP), Reg(ESP));
      (* "allocate space" for N local variables *)
      ISub(Reg(ESP), Const(4*n)); 

      ILineComment("-----start of function body-----");
      ILabel(tmp_body);
    ] in
    let postlude = [
      ILineComment("-----end of function body-----");

      (* restore value of ESP to that just before call *)
      IMov(Reg(ESP), Reg(EBP));
      (* now, value at [ESP] is caller's (saved) EBP
          so: restore caller's EBP from stack [ESP] *)
      IPop(Reg(EBP));
      (* return to caller *)
      IRet;
    ] in
    let (env, i) = List.fold_left 
      (fun (env, i) arg -> 
        let arg_reg = RegOffset((word_size * i), EBP) in
          ((arg, arg_reg)::env, i+1)
      ) ([], 2) args 
    in
    let body = compile_aexpr aexpr 1 env num_args true in
          [ ILineComment(("declaration of function " ^ fun_name));
            ILineComment(("number of arguments " ^ (string_of_int num_args)));
            ILabel(tmp); ] 
        @ prelude 
        @ body 
        @ postlude

let rec compile_prog (anfed : tag aprogram) : string =
  match anfed with
  | AProgram (adecls, aexpr, tag) -> 
    let fun_decs = List.flatten @@ List.map compile_decl adecls in
    let n = (count_vars aexpr) in
    let prelude =
    "section .text
extern error
extern print
extern printstack
extern _STACK_BOTTOM
global our_code_starts_here" in
    let prologue = [
        (* instructions for setting up stack here *)
        (* move ESP to point to a location that is N words away (so N * 4 bytes for us), 
           where N is the greatest number of variables we need at once *)
        ILabel("our_code_starts_here");
        ILineComment("-----stack setup-----");
        
        IPush(Reg(EBP));
        IMov(Reg(EBP), Reg(ESP));        
        ISub(Reg(ESP), Const(4*n)); 

        (* Set the global variable STACK_BOTTOM to EBP *)
        IMov(Variable("_STACK_BOTTOM"), Reg(EBP));
      ] 
    in

    let heap_start = [
        (* Store the HEAP to ESI, and ensure that it is a multiple of 8 *)
        (* Load ESI with the pass-in pointer *)
        IMov(Reg(ESI), RegOffset((word_size * 2), EBP));
        (* Add 7 to get above the next multiple of 8 *)
        IAdd(Reg(ESI), Const(7));
        (* Then round back down *)
        IAnd(Reg(ESI), HexConst(0xfffffff8));
       ] 
    in
    let err_handling (err_type : string) (err_code : int) : instruction list = 
        [ ILabel(err_type);
          IPush(Reg(EAX));
          IPush(Const(err_code)); 
          ICall("error");
          IAdd(Reg(ESP), Const(2*4));
          IMov(Reg(ESP), Reg(EBP)); 
          IRet;
        ]
    in
    let comp_body = 
          [ ILineComment("-----compiled code-----"); ] 
        @ (compile_aexpr aexpr 1 [] 0 false) in
    let epilogue = 
          [ ILineComment("-----epilogue-----");
            IMov(Reg(ESP), Reg(EBP)); 
            IPop(Reg(EBP));
            IRet; 
            ILineComment("-----error handling code-----")
          ]
        @ err_handling "$err_arith_not_num"      err_ARITH_NOT_NUM
        @ err_handling "$err_comparison_not_num" err_COMPARISON_NOT_NUM
        @ err_handling "$err_if_not_boolean"     err_IF_NOT_BOOL
        @ err_handling "$err_logic_not_boolean"  err_LOGIC_NOT_BOOL
        @ err_handling "$err_arith_overflow"     err_ARITH_OVERFLOW

    in
    let as_assembly_string = (to_asm (fun_decs @ prologue @ heap_start @ comp_body @ epilogue)) in
    sprintf "%s%s\n" prelude as_assembly_string


(* Feel free to add additional phases to your pipeline.
   The final pipeline phase needs to return a string,
   but everything else is up to you. *)

(* Add a desugaring phase somewhere in here, as well as your typechecker *)
let compile_to_string (prog : sourcespan program pipeline) : string pipeline =
  prog
  |> (add_err_phase well_formed is_well_formed)
  (*|> (add_err_phase type_checked type_synth)*)
  |> (add_phase desugared desugar)
  |> (add_phase tagged tag)
  |> (add_phase renamed rename_and_tag)
  |> (add_phase anfed (fun p -> atag (anf p)))
  (*|>  debug*)
  |> (add_phase result compile_prog)
;;
