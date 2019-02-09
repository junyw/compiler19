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
  let rec wf_E e (* other parameters may be needed here *) =
    Error([NotYetImplemented "Implement well-formedness checking for expressions"])
  and wf_D d (* other parameters may be needed here *) =
    Error([NotYetImplemented "Implement well-formedness checking for definitions"])
  in
  match p with
  | Program(decls, body, _) -> Ok(p)
     (*Error([NotYetImplemented "Implement well-formedness checking for programs"])*)
;;


let rec compile_fun (fun_name : string) args env : instruction list =
    failwith "compile_fun not yet implemented"


and compile_aexpr (e : tag aexpr) (si : int) (env : arg envt) (num_args : int) (is_tail : bool) : instruction list =
  match e with
  | ALet(id, cexpr, aexpr, _) -> 
     let prelude = compile_cexpr cexpr (si + 1) env num_args is_tail in
     (* id_reg: position of the binding in memory *)
     let id_reg = RegOffset(~-(word_size * si), EBP) in 
     let body = compile_aexpr aexpr (si + 1) ((id, id_reg)::env) num_args is_tail in
     prelude
     @ [ IMov(id_reg, Reg(EAX)) ]
     @ body
  | ACExpr(cexpr) -> compile_cexpr cexpr si env num_args is_tail

and compile_cexpr (e : tag cexpr) si env num_args is_tail =
  let assert_num (e_reg : arg) (error : string) = 
    [ ILineComment("assert_num");
      IMov(Reg(EAX), e_reg);
      ITest(Reg(EAX), HexConst(0x00000001));
      IJnz(error);
    ]
  (* check the value in EAX is boolean *)
  and assert_bool' (error : string) =
    [ ILineComment("assert_bool");
      IXor(Reg(EAX), HexConst(0x7FFFFFFF));
      ITest(Reg(EAX), HexConst(0x7FFFFFFF));
      IJnz(error);
      IXor(Reg(EAX), HexConst(0x7FFFFFFF));
    ]
  in 
  let assert_bool (e_reg : arg) (error : string) = 
    [ ILineComment("assert_bool");
      IMov(Reg(EAX), e_reg); 
      IXor(Reg(EAX), HexConst(0x7FFFFFFF));
      ITest(Reg(EAX), HexConst(0x7FFFFFFF));
      IMov(Reg(EAX), e_reg); 
      IJnz(error);
    ]
  in
  match e with 
  | CIf(immexpr, aexpr, aexpr2, tag) -> 
    let else_label = sprintf "if_false_%d" tag in
    let done_label = sprintf "done_%d" tag in
        [ IMov(Reg(EAX), compile_imm immexpr env) ]
      @ assert_bool' "err_if_not_boolean"
      @ [ ICmp(Reg(EAX), const_false); 
          IJe(else_label) ]
      @ compile_aexpr aexpr si env 0 false
      @ [ IJmp(done_label); 
          ILabel(else_label) ]
      @ compile_aexpr aexpr2 si env 0 false
      @ [ ILabel(done_label) ]
  | CPrim1(op, immexpr, tag) -> 
     let e = immexpr in
     let e_reg = compile_imm e env in
     let done_label = sprintf "eprim1_done_%d" tag in
     begin match op with
     | Add1  -> assert_num e_reg "err_arith_not_num" @
                [ IMov(Reg(EAX), e_reg);
                  IAdd(Reg(EAX), Const(1 lsl 1)); 
                  (* check overflow *) 
                  IJo("err_arith_overflow");
                ] 
     | Sub1  -> assert_num e_reg "err_arith_not_num" @
                [ IMov(Reg(EAX), e_reg); 
                  IAdd(Reg(EAX), Const(~-1 lsl 1));
                  (* check overflow *) 
                  IJo("err_arith_overflow");
                ] 
     | Print -> [ ILineComment("calling c function");
                  ISub(Reg(ESP), Const(8)); (* stack padding *)
                  IPush(Sized(DWORD_PTR, e_reg)); 
                  ICall("print");
                  IAdd(Reg(ESP), Const(3*4));
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
          assert_bool e_reg "err_logic_not_boolean" 
        @ [ IMov(Reg(EAX), e_reg);
            IXor(Reg(EAX), Const(0x80000000));
          ]
     | PrintStack -> failwith "eprim1 not implemented"
     end
  | CPrim2(op, imme1, imme2, tag) -> 
     let e1 = imme1 in
     let e2 = imme2 in (* TODO: rename variables *)
     let e1_reg = compile_imm e1 env in
     let e2_reg = compile_imm e2 env in
     let done_label = sprintf "eprim2_done_%d" tag in
     begin match op with 
     | Plus  -> 
        assert_num e1_reg "err_arith_not_num" @
        assert_num e2_reg "err_arith_not_num" @
        [ IMov(Reg(EAX), e1_reg); 
          IAdd(Reg(EAX), e2_reg);
          (* check overflow *) 
          IJo("err_arith_overflow");

        ]
     | Minus -> 
          assert_num e1_reg "err_arith_not_num"
        @ assert_num e2_reg "err_arith_not_num"
        @ [ IMov(Reg(EAX), e1_reg); 
            ISub(Reg(EAX), e2_reg);
            (* check overflow *) 
            IJo("err_arith_overflow");
          ]
     | Times -> 
          assert_num e1_reg "err_arith_not_num"
        @ assert_num e2_reg "err_arith_not_num"
        @ [ IMov(Reg(EAX), e1_reg); 
            ISar(Reg(EAX), Const(1));
            IMul(Reg(EAX), e2_reg);
            (* check overflow *) 
            IJo("err_arith_overflow");
          ]
     | And   -> 
          assert_bool e1_reg "err_logic_not_boolean" 
        @ assert_bool e2_reg "err_logic_not_boolean" 
        @ [ IMov(Reg(EAX), e1_reg); 
            IAnd(Reg(EAX), e2_reg); 
          ]
     | Or    -> 
          assert_bool e1_reg "err_logic_not_boolean" 
        @ assert_bool e2_reg "err_logic_not_boolean" 
        @ [ IMov(Reg(EAX), e1_reg); 
            IOr(Reg(EAX),  e2_reg);
          ]
     | Greater ->
          assert_num e1_reg "err_comparison_not_num"
        @ assert_num e2_reg "err_comparison_not_num"
        @ [ IMov(Reg(EAX), e1_reg);
            ICmp(Reg(EAX), e2_reg);
            IMov(Reg(EAX), const_true);
            IJg(done_label);
            IMov(Reg(EAX), const_false);
            ILabel(done_label);
          ]
     | GreaterEq ->
          assert_num e1_reg "err_comparison_not_num"
        @ assert_num e2_reg "err_comparison_not_num"
        @ [ IMov(Reg(EAX), e1_reg);
            ICmp(Reg(EAX), e2_reg);
            IMov(Reg(EAX), const_true);
            IJge(done_label);
            IMov(Reg(EAX), const_false);
            ILabel(done_label);
          ]
     | Less  -> 
          assert_num e1_reg "err_comparison_not_num"
        @ assert_num e2_reg "err_comparison_not_num"
        @ [ IMov(Reg(EAX), e1_reg);
            ICmp(Reg(EAX), e2_reg);
            IMov(Reg(EAX), const_true);
            IJl(done_label);
            IMov(Reg(EAX), const_false);
            ILabel(done_label);
          ]
     | LessEq ->
          assert_num e1_reg "err_comparison_not_num"
        @ assert_num e2_reg "err_comparison_not_num"
        @ [ IMov(Reg(EAX), e1_reg);
            ICmp(Reg(EAX), e2_reg);
            IMov(Reg(EAX), const_true);
            IJle(done_label);
            IMov(Reg(EAX), const_false);
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
  | CApp(fun_name, immexprs, tag) ->  (* TODO: handle functions of different arities *)
    let imm_regs = List.map (fun expr -> compile_imm expr env) immexprs in
    (* the label of the function declaration *)
    let tmp = sprintf "fun_dec_%s" fun_name 
    in
      [ ILineComment(("calling function " ^ fun_name ^ ": " ^tmp));
        ISub(Reg(ESP), Const(8)); (* stack padding *)
        IPush(Sized(DWORD_PTR, List.hd imm_regs)); (* TODO: fix *) 
        ICall(tmp);
        IAdd(Reg(ESP), Const(3*4));
      ]
  | CImmExpr(immexpr) -> [ IMov(Reg(EAX), compile_imm immexpr env) ]
and compile_imm e env : arg =
  match e with
  | ImmNum(n, _) -> 
       if n > 1073741823 || n < -1073741824 then
       failwith ("Compile-time integer overflow: " ^ (string_of_int n))
     else
       Const(n lsl 1)
  | ImmBool(true, _) -> const_true
  | ImmBool(false, _) -> const_false
  | ImmId(x, _) -> (find env x)

and compile_decl (d : tag adecl) : instruction list =
  match d with 
  | ADFun(name, args, aexpr, tag) ->
    let tmp = sprintf "fun_dec_%s" name in
    let n = (count_vars aexpr) in
    let prelude = [
      (* save (previous, caller's) EBP on stack *)
      IPush(Reg(EBP));
      (* make current ESP the new EBP *)
      IMov(Reg(EBP), Reg(ESP));
      (* "allocate space" for N local variables *)
      ISub(Reg(ESP), Const((4*n/16+1)*16)); (* make esp 16-byte aligned *)

      ILineComment("-----start of function body-----");

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
    let body = compile_aexpr aexpr 0 env (List.length args) false in
          [ ILineComment(("declaration of function " ^ name));
            ILabel(tmp); ] 
        @ prelude 
        @ body 
        @ postlude

let rec compile_prog (anfed : tag aprogram) : string =
  match anfed with
  | AProgram (adecls, aexpr, tag) -> 
    let fun_decs = List.flatten(List.map compile_decl adecls) in
    let n = (count_vars aexpr) in
    let prelude =
    "section .text
extern error
extern print
global our_code_starts_here" in
    let stack_setup = [
        (* instructions for setting up stack here *)
        (* move ESP to point to a location that is N words away (so N * 4 bytes for us), 
           where N is the greatest number of variables we need at once*)
        ILabel("our_code_starts_here");
        ILineComment("-----stack setup-----");
        
        IMov(Reg(EBP), Reg(ESP)); 
        ISub(Reg(ESP), Const((4*n/16+1)*16)); (* make esp 16-byte aligned *)

        ILineComment("-----compiled code-----");
      ] in
    let err_handling (err_type : string) (err_code : int) : instruction list = 
        [ ILabel(err_type);
          IPush(Const(0));
          IPush(Reg(EAX));
          IPush(Const(err_code)); 
          ICall("error");
          IAdd(Reg(ESP), Const(3*4));
          IMov(Reg(ESP), Reg(EBP)); 
          IRet;
        ]
    in
    let postlude = [
        ILineComment("-----postlude-----");
        IMov(Reg(ESP), Reg(EBP)); 
        IRet; ]
        (* error handling *)
        @ (err_handling "err_arith_not_num" 1)
        @ err_handling "err_comparison_not_num" 2
        @ err_handling "err_if_not_boolean" 3
        @ err_handling "err_logic_not_boolean" 4
        @ err_handling "err_arith_overflow" 5
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
  |> (add_phase anfed (fun p -> atag (anf p)))
  |> (add_phase result compile_prog)
;;
