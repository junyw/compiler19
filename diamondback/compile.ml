open Printf
open Pretty
open Phases
open Exprs
open Assembly
open Errors
       
type 'a envt = (string * 'a) list

let rec is_anf (e : 'a expr) : bool =
  match e with
  | EPrim1(_, e, _) -> is_imm e
  | EPrim2(_, e1, e2, _) -> is_imm e1 && is_imm e2
  | ELet(binds, body, _) ->
     List.for_all (fun (_, e, _) -> is_anf e) binds
     && is_anf body
  | EIf(cond, thn, els, _) -> is_imm cond && is_anf thn && is_anf els
  | EApp(f, args, _) -> List.for_all is_imm args
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
     if String.equal y x then v else find rest x

let rec find_opt ls x =
  match ls with
  | [] -> None
  | (y,v)::rest ->
     if String.equal y x then Some(v) else find_opt rest x

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
    | (DFun(fname, _, _, _) as d)::ds_rest ->
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

(* IMPLEMENT EVERYTHING BELOW *)



let anf (p : tag program) : unit aprogram =
  let rec helpP (p : tag program) : unit aprogram =
    match p with
    | Program(decls, body, _) -> AProgram(List.map helpD decls, helpA body, ())
  and helpD (d : tag decl) : unit adecl =
    match d with
    | DFun(name, args, body, _) -> ADFun(name, List.map fst args, helpA body, ())
  and helpC (e : tag expr) : (unit cexpr * (string * unit cexpr) list) = 
    match e with
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
    | ELet((bind, exp, _)::rest, body, pos) ->
       let (exp_ans, exp_setup) = helpC exp in
       let (body_ans, body_setup) = helpC (ELet(rest, body, pos)) in
       (body_ans, exp_setup @ [(bind, exp_ans)] @ body_setup)
    | EApp(funname, args, _) ->
       let (args_imm, args_setup) = 
          List.fold_left
          (fun (args_imm, args_setup) arg -> 
            let (arg_imm, arg_setup) = helpI arg in 
                (arg_imm::args_imm, arg_setup @ args_setup)
          )
          ([], []) args
       in
       (CApp(funname, args_imm, ()), args_setup)
    | _ -> let (imm, setup) = helpI e in (CImmExpr imm, setup)

  and helpI (e : tag expr) : (unit immexpr * (string * unit cexpr) list) =
    match e with
    | ENumber(n, _) -> (ImmNum(n, ()), [])
    | EBool(b, _) -> (ImmBool(b, ()), [])
    | EId(name, _) -> (ImmId(name, ()), [])
    | EPrim1(op, arg, tag) ->
       let tmp = sprintf "$unary_%d" tag in
       let (arg_imm, arg_setup) = helpI arg in
       (ImmId(tmp, ()), arg_setup @ [(tmp, CPrim1(op, arg_imm, ()))])
    | EPrim2(op, left, right, tag) ->
       let tmp = sprintf "$binop_%d" tag in
       let (left_imm, left_setup) = helpI left in
       let (right_imm, right_setup) = helpI right in
       (ImmId(tmp, ()), left_setup @ right_setup @ [(tmp, CPrim2(op, left_imm, right_imm, ()))])
    | EIf(cond, _then, _else, tag) ->
       let tmp = sprintf "$if_%d" tag in
       let (cond_imm, cond_setup) = helpI cond in
       (ImmId(tmp, ()), cond_setup @ [(tmp, CIf(cond_imm, helpA _then, helpA _else, ()))])
    | EApp(funname, args, tag) -> 
       let tmp = sprintf "$app_%d" tag in
       let (args_imm, args_setup) = 
          List.fold_left
          (fun (args_imm, args_setup) arg -> 
            let (arg_imm, arg_setup) = helpI arg in 
                (arg_imm::args_imm, arg_setup @ args_setup)
          )
          ([], []) args
       in
       (ImmId(tmp, ()), args_setup @ [(tmp, CApp(funname, args_imm, ()))])
    | ELet([], body, _) -> helpI body
    | ELet((bind, exp, _)::rest, body, pos) ->
       let (exp_ans, exp_setup) = helpC exp in
       let (body_ans, body_setup) = helpI (ELet(rest, body, pos)) in
       (body_ans, exp_setup @ [(bind, exp_ans)] @ body_setup)
  and helpA e : unit aexpr = 
    let (ans, ans_setup) = helpC e in
    List.fold_right (fun (bind, exp) body -> ALet(bind, exp, body, ())) ans_setup (ACExpr ans)
  in
  helpP p
;;

let is_well_formed (p : sourcespan program) : (sourcespan program) fallible =
  let rec wf_E (e : sourcespan expr) env fun_env: exn list = 
      let rec wf_E' (env : sourcespan envt) (fun_env : sourcespan decl envt) (e : sourcespan expr) (errors : exn list) : exn list = 
        match e with
        | EBool _ -> errors
        | ENumber(n, loc) -> if n > 1073741823 || n < -1073741824 then
                               errors @ [ Overflow(n, loc) ]
                             else errors
        | EId(x, loc) ->
          begin match List.assoc_opt x env with
            | None -> errors @ [ UnboundId(x, loc) ]
            | Some(_) -> errors
          end
        | EPrim1(_, e, _) -> wf_E' env fun_env e errors
        | EPrim2(_, l, r, _) -> errors |> wf_E' env fun_env l |> wf_E' env fun_env r
        | EIf(c, t, f, _) -> errors |> wf_E' env fun_env c |> wf_E' env fun_env t |> wf_E' env fun_env f
        | ELet(binds, body, _) ->
          let name_locs = List.map (fun (binding_name, _, loc) -> (binding_name, loc)) binds in
            errors 
            (* check duplicate bindings *)
          @ check_duplicates name_locs
            (* check bindings: TODO *)
          @  let (errors, new_env)  = 
                List.fold_left 
                (fun (errors, env) (id, binding_body, loc)  -> 
                   (errors |> wf_E' env fun_env binding_body, (id, loc)::env)) 
                ([], env) binds
             in errors
            (* check body *)
          @ wf_E body new_env fun_env
        | EApp(f, args, loc) -> 
          match find_opt fun_env f with
          | None -> errors @ [ UnboundFun(f, loc) ]
          | Some(DFun(_, args', _, _)) ->
              if List.length args' != List.length args
              then errors @ [ Arity(List.length args', List.length args, loc) ]
              else errors
      in wf_E' env fun_env e  []
  and check_duplicates (args : (string * sourcespan) list) : exn list =
    let (errs, _) = 
            List.fold_left 
            (fun (errs, args_list) (arg_name, source2) -> 
              match (find_opt args_list arg_name) with
              | Some(duplicate_source) -> (errs @ [ DuplicateId(arg_name, source2, duplicate_source) ], args_list)
              | None -> (errs, args_list @ [(arg_name, source2)])
            ) ([], []) args
    in
    errs 
  and wf_D (fun_env : sourcespan decl envt) (d : sourcespan decl) = 
    match d with
    | DFun(fun_name, args, body,  _) ->
      check_duplicates args @ wf_E body args fun_env
  in
  match p with
  | Program(decls, body, _) -> 
    let fun_env : sourcespan decl envt = List.map (fun decl -> match decl with | DFun(fun_name, _, _, _) -> (fun_name, decl)) decls in
    (* check duplicate function declarations *)
    let duplicate_decls = check_duplicates (List.map (fun decl -> match decl with | DFun(fun_name, _, _, loc) -> (fun_name, loc)) decls) in
    (* check well-formedness in function declartions *)
    let decls_err = List.flatten @@ List.map (wf_D fun_env) decls in
    (* check well-formedness in body *)
    let body_err = wf_E body [] fun_env in
    if List.length duplicate_decls == 0 && List.length decls_err == 0 && List.length body_err == 0
      then Ok(p)
      else Error(duplicate_decls @ decls_err @ body_err)
;;

(* alpha-renaming, called after well-formedness check *)
let rename (prog : tag program) : tag program = 
  let rec renameE (env : string envt) (e: tag expr) : tag expr = 
    match e with
    | ENumber _ -> e
    | EBool _   -> e
    | EId(id, tag) -> EId(find env id, tag)
    | EPrim1(op, e1, tag) -> EPrim1(op, renameE env e1, tag)
    | EPrim2(op, e1, e2, tag) -> EPrim2(op, renameE env e1, renameE env e2, tag)
    | EIf(cond, thn, els, tag) -> EIf(renameE env cond, renameE env thn, renameE env els, tag)
    | ELet(binds, body, tag) ->
        let help (binds, env) (name, exp, tag) : (tag bind list * string envt) = 
          let new_name = sprintf "$%s_%d" name tag in
          let new_exp = renameE env exp in
          let new_env = (name, new_name)::env in
          ((new_name, new_exp, tag)::binds, new_env)
        in
          let (new_binds, new_env) = List.fold_left help ([], env) binds
        in ELet((List.rev new_binds), renameE new_env body, tag)
    | EApp(fun_name, args, tag) -> EApp(fun_name, List.map (renameE env) args, tag)
  in
  let rename_decl (decl: 'a decl) : 'a decl =  
    match decl with
    | DFun(fun_id, args, body, tag) -> 
        let args_env = List.map (fun (x, y) -> (x, x)) args in
          DFun(fun_id, args, renameE args_env body, tag)
  in
    match prog with
    | Program(decls, expr, tag) -> 
      Program(List.map rename_decl decls , renameE [] expr, tag)



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
     let e = immexpr in
     let e_reg = compile_imm e env in
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
     | IsBool -> 
        [ IMov(Reg(EAX), e_reg); 
          IAnd(Reg(EAX), Const(0x7FFFFFFF));
          ICmp(Reg(EAX), Const(0x7FFFFFFF));
          IMov(Reg(EAX), const_true);
          IJe(done_label);
          IMov(Reg(EAX), const_false);
          ILabel(done_label);
        ]
     | IsNum  -> 
        [ IMov(Reg(EAX), e_reg); 
          IAnd(Reg(EAX), Const(0x00000001)); 
          ICmp(Reg(EAX), Const(0));
          IMov(Reg(EAX), const_true);
          IJe(done_label);
          IMov(Reg(EAX), const_false);
          ILabel(done_label);
        ];
      | Not  ->
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
     end
  | CApp(fun_name, immexprs, tag) ->
    let imm_regs = List.map (fun expr -> compile_imm expr env) immexprs in
    (* the label of the function declaration *)
    let tmp = sprintf "$fun_dec_%s" fun_name in
    let tmp_body = sprintf "$fun_dec_body_%s" fun_name in
    let num_of_args = List.length immexprs in
    if is_tail && num_of_args == num_args (* TODO *)
    then
      let (_, push_args) = List.fold_right (fun imm_reg (i, instrs) -> 
          (i + 1, 
           [ IPush(Sized(DWORD_PTR, imm_reg)) ] @ instrs @ [ IPop(Sized(DWORD_PTR, RegOffset((word_size * i), EBP))) ])
        ) imm_regs (2, [])
      in
        [ ILineComment(sprintf "calling %s(%s) of %d arguments" fun_name tmp num_of_args);
          ILineComment(sprintf "caller has %d arguments" num_args);
          ILineComment(("tail call: " ^ (string_of_bool is_tail)));
        ] 
        @ push_args @
        [
          IJmp(tmp_body);
        ]
    else
      let push_args = List.fold_right (fun imm_reg instrs -> 
          [ IPush(Sized(DWORD_PTR, imm_reg)) ] @ instrs
        ) imm_regs []
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
    let stack_setup = [
        (* instructions for setting up stack here *)
        (* move ESP to point to a location that is N words away (so N * 4 bytes for us), 
           where N is the greatest number of variables we need at once*)
        ILabel("our_code_starts_here");
        ILineComment("-----stack setup-----");
        
        IMov(Reg(EBP), Reg(ESP));        
        ISub(Reg(ESP), Const(4*n)); 

        (* Set the global variable STACK_BOTTOM to EBP *)
        IMov(Variable("_STACK_BOTTOM"), Reg(EBP));

        ILineComment("-----compiled code-----");
      ] in
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
    let postlude = 
          [ ILineComment("-----postlude-----");
            IMov(Reg(ESP), Reg(EBP)); 
            IRet; 
            ILineComment("-----error handling code-----")
          ]
        @ err_handling "$err_arith_not_num"      err_ARITH_NOT_NUM
        @ err_handling "$err_comparison_not_num" err_COMPARISON_NOT_NUM
        @ err_handling "$err_if_not_boolean"     err_IF_NOT_BOOL
        @ err_handling "$err_logic_not_boolean"  err_LOGIC_NOT_BOOL
        @ err_handling "$err_arith_overflow"     err_ARITH_OVERFLOW

    in
    let body = (compile_aexpr aexpr 1 [] 0 false) in
    let as_assembly_string = (to_asm (fun_decs @ stack_setup @ body @ postlude)) in
    sprintf "%s%s\n" prelude as_assembly_string

(* Feel free to add additional phases to your pipeline.
   The final pipeline phase needs to return a string,
   but everything else is up to you. *)
let compile_to_string (prog : sourcespan program pipeline) : string pipeline =
  prog
  |> (add_err_phase well_formed is_well_formed)
  |> (add_phase tagged tag)
  |> (add_phase renamed rename)
  |> (add_phase anfed (fun p -> atag (anf p)))
  |> (add_phase result compile_prog)
;;
