open Exprs
open Errors
open Printf
open Pretty
open Phases

let show_debug_print = ref false
let debug_printf fmt =
  if !show_debug_print
  then printf fmt
  else ifprintf stdout fmt
;;

module StringMap = Map.Make(String);;
module StringSet = Set.Make(String);;

type 'a envt = 'a StringMap.t;;
type 'a subst = (string * 'a) list;;

let print_funenv funenv =
  StringMap.iter (fun name scheme -> printf "\t%s => %s\n" name (string_of_scheme scheme)) funenv;;
let print_env env =
  StringMap.iter (fun name typ -> debug_printf "\t%s => %s\n" name (string_of_typ typ)) env;;

let print_subst subst =
  List.iter (fun (name, typ) -> debug_printf "\t%s => %s\n" name (string_of_typ typ)) subst;;

let dummy_span = (Lexing.dummy_pos, Lexing.dummy_pos)
let mk_tyvar (label: string) : 'a typ = 
    TyVar(label, dummy_span)
;;
let mk_tyarr left right : 'a typ = 
    TyArr(left, right, dummy_span)
;;
let mk_scheme (ids : string list) typ =
    SForall(ids, typ, dummy_span)

let tInt = TyCon("Int", dummy_span)
let tBool = TyCon("Bool", dummy_span)
let tNil = TyCon("Nil", dummy_span)

(*  forall,  Int -> Int *)
let int2int = SForall([], mk_tyarr [tInt] tInt, dummy_span)

(*  forall,  Int * Int -> Int *)
let intint2int = SForall([], mk_tyarr [tInt; tInt] tInt, dummy_span)

(*  forall,  Int -> Bool *)
let int2bool = SForall([], mk_tyarr [tInt] tBool, dummy_span)

(*  forall,  Bool -> Bool *)
let bool2bool = SForall([], mk_tyarr [tBool] tBool, dummy_span)

(*  forall,  Bool * Bool -> Bool *)
let boolbool2bool = SForall([], mk_tyarr [tBool; tBool] tBool, dummy_span)

(*  forall,  Int * Int -> Bool *)
let intint2bool = SForall([], mk_tyarr [tInt; tInt] tBool, dummy_span)

let tyVarX = TyVar("X", dummy_span)
let tyVarY = TyVar("Y", dummy_span)
let tyVarZ = TyVar("Z", dummy_span)

(* forall X, X -> Bool *)
let any2bool = SForall(["X"], mk_tyarr [tyVarX] tBool, dummy_span)

(* forall X, X -> X *)
let any2any = SForall(["X"], mk_tyarr [tyVarX] tyVarX, dummy_span)

(* forall X Y, X -> Y *)
let arrX2Y = SForall(["X";"Y"], mk_tyarr [tyVarX] tyVarY, dummy_span)

(* forall X Y Z, X Y -> Z *)
let arrXY2Z = SForall(["X";"Y";"Z"], mk_tyarr [tyVarX; tyVarY] tyVarZ, dummy_span)


(* initial function environment *)
let initial_env : sourcespan scheme envt =
  List.fold_left (fun env (name, typ) -> StringMap.add name typ env) StringMap.empty [

      (* prim1 functions *)      
      ("Add1", int2int);
      ("Sub1", int2int);
      ("Print", arrX2Y); 
      ("PrintStack", arrX2Y);
      ("Not",    bool2bool);
      ("IsNum",  any2bool);
      ("IsBool", any2bool);
      ("IsTuple", any2bool);
      ("Input", any2any);

      (* prim2 functions *)      
      ("Plus",  intint2int);
      ("Minus", intint2int);
      ("Times", intint2int);
      ("And", boolbool2bool);
      ("Or",  boolbool2bool);
      ("Greater", intint2bool);
      ("Less", intint2bool);
      ("GreaterEq", intint2bool);
      ("LessEq", intint2bool);
      ("Eq", SForall(["X"], mk_tyarr [tyVarX; tyVarX] tBool, dummy_span));
  ]

let gensym =
  let count = ref 0 in
  let next () =
    count := !count + 1;
    !count
  in fun str -> sprintf "%s_%d" str (next ());;

(* subst_var_typ: converts each occurrence of the given type variable tyvar 
    into the desired type to_typ in the target type in_typ *)
let rec subst_var_typ (((tyvar : string), (to_typ : 'a typ)) as sub) (in_typ : 'a typ): 'a typ =
  match in_typ with 
  | TyBlank _ -> in_typ 
  | TyCon _ -> in_typ
  | TyVar(tyvar1, _) -> if String.equal tyvar tyvar1 then to_typ else in_typ
  | TyArr(typs, typ, tag) ->
    let typs_subst = List.map (fun typ -> subst_var_typ sub typ) typs in
    let typ_subst = subst_var_typ sub typ in
        TyArr(typs_subst, typ_subst, tag)
  | TyApp(typ, typs, _) -> failwith "subst_var_typ: TyApp not implemented" 
  | TyTup(typs, tag) -> 
    let typs = List.map (fun typ -> subst_var_typ sub typ) typs in
      TyTup(typs, tag)
;;

let subst_var_scheme ((tyvar, to_typ) as sub) scheme =
  match scheme with (* ?? *)
    | SForall(strings, typ, loc) -> SForall(strings, subst_var_typ sub typ, loc)
;;
let apply_subst_typ (subst : 'a typ subst) (t : 'a typ) : 'a typ =
  List.fold_left (fun t sub -> subst_var_typ sub t) t subst
;;

let apply_subst_scheme (subst : 'a typ subst) (scheme : 'a scheme) : 'a scheme =
  List.fold_left (fun scheme sub -> subst_var_scheme sub scheme) scheme subst
;;

let apply_subst_env (subst : 'a typ subst) (env : 'a typ envt) : 'a typ envt =
  StringMap.fold 
  (fun name typ new_env -> StringMap.add name (apply_subst_typ subst typ) new_env)
  env StringMap.empty
;;

let apply_subst_funenv (subst : 'a typ subst) (env : 'a scheme envt) : 'a scheme envt =
  StringMap.fold 
  (fun name scheme new_env -> StringMap.add name (apply_subst_scheme subst scheme) new_env)
  env StringMap.empty
;;

let apply_subst_subst (subst : 'a typ subst) (dest : 'a typ subst) : 'a typ subst =
  List.map (fun (tyvar, typ) -> (tyvar, apply_subst_typ subst typ)) dest
;;

let compose_subst (sub1 : 'a typ subst) (sub2 : 'a typ subst) : 'a typ subst =
  sub1 @ (apply_subst_subst sub1 sub2)
;;

(* free type variables of a type as the set of any type variables that appear within it *)
let rec ftv_type (t : 'a typ) : StringSet.t =
  match t with
  | TyBlank _ -> StringSet.empty
  | TyCon _ -> StringSet.empty
  | TyVar(name, _) -> StringSet.singleton name
  | TyArr(args, ret, _) ->
    List.fold_right (fun t ftvs -> StringSet.union (ftv_type t) ftvs)
                    args
                    (ftv_type ret)
  | TyApp(typ, args, _) ->
    List.fold_right (fun t ftvs -> StringSet.union (ftv_type t) ftvs)
                    args
                    (ftv_type typ)
  | TyTup(typs, tag) -> 
    List.fold_right (fun t ftvs -> StringSet.union (ftv_type t) ftvs)
                    typs
                    StringSet.empty

;;
let ftv_scheme (s : 'a scheme) : StringSet.t =
  match s with
  | SForall(args, typ, _) ->
     StringSet.diff (ftv_type typ) (StringSet.of_list args)
let ftv_env (e : 'a typ envt) : StringSet.t = 
  failwith "Compute the free type variables of an environment here"
;;
(*let bind (tyvarname : string) (t : 'a typ) : 'a typ subst =
  match t with
  | TyVar(name, _) when tyvarname = name -> []
  | _ ->
     if StringSet.mem tyvarname (ftv_type t)
     then raise (OccursCheck (sprintf "Infinite types: %s occurs in %s" tyvarname (string_of_typ t)))
     else [(tyvarname, t)]
;;

*)


(* unify:
   given two types t1 and t2, and a pre-existing substitution sub,
   returns the most general substitution sub' which extends sub 
   and makes two given types equal
*)
exception OccursCheck of string

let rec unify (t1 : 'a typ) (t2 : 'a typ) (sub : 'a typ subst) (loc : sourcespan) (reasons : reason list) : 'a typ subst =  
  let occurs (name : string) (t : 'a typ) =
    StringSet.mem name (ftv_type t)
  in
  (* unfiy_typs: helper function that unify two list of types *)
  let unfiy_typs (typs1 : 'a typ list) (typs2 : 'a typ list) (sub : 'a typ subst) loc reasons : 'a typ subst = 
      List.fold_left2
      (fun sub t1 t2 -> unify t1 t2 sub loc reasons)
      sub typs1 typs2 
  in
    let t1 = apply_subst_typ sub t1
      , t2 = apply_subst_typ sub t2 
    in
    match (t1, t2) with 
    | (TyVar(id1, _), TyVar(id2, _)) when (String.equal id1 id2) -> sub
    | (TyVar(id1, _), t2) when not (occurs id1 t2) -> (* extend sub *) apply_subst_subst [(id1, t2)] sub
    | (_, TyVar(id2, _)) -> unify t2 t1 sub loc reasons
    | (TyArr(typs1, typ1, _), TyArr(typs2, typ2, _)) -> 
        (* unify argument types *)
        let sub = unfiy_typs typs1 typs2 sub loc reasons in 
        (* unify the return type *)
        unify typ1 typ2 sub loc reasons 
    | (TyTup(typs1, _), TyTup(typs2, _)) -> 
        (* unify tuple element types *)
        unfiy_typs typs1 typs2 sub loc reasons 
    | (TyCon(id1, _), TyCon(id2, _)) when (String.equal id1 id2) -> sub
    | _ -> raise (TypeMismatch(loc, t2, t1, reasons))
;;     
     

(* Eliminates all `TyBlank`s in a type, and replaces them with fresh type variables *)
let rec unblank (t : 'a typ) : 'a typ =
  match t with
  | TyBlank tag -> 
      (* create fresh type variable *)
      TyVar(gensym "blank", tag)
  | TyCon _ -> t
  | TyVar _ -> t
  | TyArr(args, ret, tag) ->
     let args = List.map unblank args in
     let ret = unblank ret in TyArr(args, ret, tag)
  | TyApp(t, args, tag) ->
     let t = unblank t in
     let args = List.map unblank args in TyApp(t, args, tag)
  | TyTup(typs, tag) -> 
     let typs = List.map unblank typs in TyTup(typs, tag)
;;

let instantiate (s : 'a scheme) : 'a typ =
  match s with
  | SForall(vars, typ, loc) -> 
    (* if there are blanks, replace it with a fresh type variable *)
    let typ = unblank typ in
    let subst = 
      List.fold_left
      (fun subst var -> 
        let tyvar = TyVar(gensym "fun", loc) in
          (var, tyvar)::subst
      ) [] vars
    in
    let ins_typ = apply_subst_typ subst typ in
      ins_typ
;;

let generalize (e : 'a typ envt) (t : 'a typ) : 'a scheme =
  (* generalize_typ: decides if a type needs to be generalized 
      if the type variable is not present in env, add it to env and some.
  *)
  let rec generalize_typ (env, (some : string list)) (t : 'a typ) = 
    match t with
    | TyVar(x, _) -> 
      (* if type t is not in the environment, add the type to some and env *)
      begin match StringMap.find_opt x env with
      | Some _ -> (env, some)
      | None   -> (StringMap.add x t env, x::some)
      end 
    | TyCon _   -> (env, some)
    | TyArr _   -> failwith "generalize_typ: TyArr not implemented - higher order function is not implemented"
    | TyBlank _ -> failwith "generalize_typ: TyBlank - should unblank first"
    | TyApp _   -> failwith "generalize_typ: TyApp - impossible case"
    | TyTup(typs, _) -> 
        List.fold_left generalize_typ (env, some) typs
  in
  match t with 
  | TyArr(arg_typs, b_typ, loc) -> 
    let (e_new, some) = 
        List.fold_left
        generalize_typ (e, []) arg_typs
    in
    let (_, some) = generalize_typ (e_new, some) b_typ in
      SForall(some, t, loc)
  | _ -> failwith "generalize: impossible case"
;;



(* infer_exp
   env: environment that associate variable names with types
   t: a proto-type
   e: expression
   funenv: environment that associate function names with type schemes
   s: pre-existing substitution
  
   returns: a new substitution s' that extends s
*)
let rec infer_exp 
          (funenv : sourcespan scheme envt) 
          (env : sourcespan typ envt) 
          (t : 'a typ)
          (e : sourcespan expr) 
          (sub  : 'a typ subst) 
          reasons
        : sourcespan typ subst =
  (* find_pos: find type of vairable from environment, or find type scheme of function from funenv *)
  let rec find_pos (ls : 'a envt) x pos : 'a =
    try
      StringMap.find x ls
    with
    | Not_found -> failwith (sprintf "inference.ml: type of variable %s not found at %s" x (string_of_sourcespan pos))
  in
  (* infer_app: infer type of function call, including primitive function calls *)
  let infer_app (e : 'a expr)  
        : (sourcespan typ subst * sourcespan typ) =
      let (fun_name, args, loc) =
         match e with
         | EPrim1(op, expr, loc) -> (name_of_op1 op, [expr], loc)
         | EPrim2(op, expr1, expr2, loc) -> (name_of_op2 op, [expr1; expr2], loc) 
         | EApp(fun_name, args, loc) -> (fun_name, args, loc)
         | _ -> failwith "infer_app: impossible expr"
      in
      (* lookup function scheme from funenv *)
      let scheme = find_pos funenv fun_name loc in
      (* fun_ty: type of the function *)
      let fun_ty = instantiate scheme in
      (* generate a new type variable as return type *)
      let ret_ty = TyVar(gensym "arg", loc) in

      (* type the arguments *)
      let (arg_substs, args_typs) = 
         List.fold_left 
         (fun (subst_so_far, args_typs) arg -> 
            let (arg_subst, arg_typ, arg, _) = infer_exp funenv env sub arg reasons in 
            (compose_subst arg_subst subst_so_far, args_typs@[arg_typ])
         ) ([], []) args
      in
      (* type of the function call *)
      let app_typ = TyArr(args_typs, ret_ty, loc) in
      let app_typ = apply_subst_typ arg_substs app_typ in
  in
  match e with
  | ENumber(v, loc) -> apply_subst_subst [(t, tInt)] s
  | EBool(v, loc)   -> apply_subst_subst [(t, tBool)] s
  | EId(x, loc)     -> let a = find_pos env x loc in
                           unify(a, t, s)

  | ELet([], e, loc) -> infer_exp funenv env t e s reasons
  | ELet((x, e1, _)::rest, e2, loc) -> 
    begin match x with
    | BName(name, typ, _) -> 
        (* generate a fresh type for typ, if it is blank *)
        let a = unblank typ in
        (* type the binding *)
        let (sub1, _) = infer_exp funenv env sub e reasons in
        (* type the rest *)
        infer_exp funenv (StringMap.add name (apply_subst_typ sub1 a) env) sub1 (ELet(rest, expr, loc)) reasons
    | BTuple(binds, _) -> (* TODO *)
    | BBlank(typ, _)   -> failwith "infer_expr: impossible binding type"
    end

  | ELet(bindings, aexpr, loc) -> 
    let rec infer_tuple (bind, expr, loc) env
        : (sourcespan typ subst * sourcespan typ * sourcespan expr * sourcespan typ envt) = 
      let (subst, typ, expr) = infer_exp' funenv env expr reasons in
      begin match bind with
      | BTuple(binds, _) -> 
        let (tuple_subst, tuple_typ, _, env) = infer_exp tyenv funenv env expr reasons in
        let tuple_typ = unblank tuple_typ in
        begin match expr with
              | ETuple(tuple_exprs, a) -> 
                let env' =
                  List.fold_left2 
                  (fun env bind t_expr -> 
                        match bind with
                        | BTuple(binds, loc') -> let (_, _, _, env') = infer_tuple (bind, t_expr, loc') env in env'
                        | BBlank(typ, _)   -> env
                        | BName(name, typ, _) -> StringMap.add name (unblank typ) env
                  ) env binds tuple_exprs
                in (subst, tuple_typ, expr, env')
              | EId _ -> 
                let env' =
                  List.fold_left 
                  (fun env bind -> 
                        match bind with
                        | BTuple(binds, loc') -> let (_, _, _, env') = infer_tuple (bind, expr(*?*), loc') env in env'
                        | BBlank(typ, _)   -> env
                        | BName(name, typ, _) -> StringMap.add name (unblank typ) env
                  ) env binds
                in (subst, tuple_typ, expr, env')
              | _ -> failwith ("infer_tuple: impossible type" ^ (string_of_expr_with string_of_sourcespan expr))
        end
      | BBlank(typ, loc)   -> ([], TyBlank(loc), expr, env)
      | BName(name, typ', _) -> 
        (* TODO *)
        ([], typ, expr, StringMap.add name typ' env)
      end
    in
    let (new_env, binds_subst) = 
        List.fold_left 
        (fun (env, subst) (bind, expr, loc') -> 
            match bind with
            | BBlank(typ, _) -> (env, subst) (* TODO *)
            | BName(name, typ, _) -> 
              (* type the binding *)
              let (binding_subst, binding_typ, expr) = infer_exp' funenv env expr reasons in
              (* typ is the user provided type annotation, maybe blank *)
              let typ = unblank typ in
              (* unification *)
              let subst0 = unify tyenv binding_typ typ loc' reasons in 
              let subst_so_far = compose_subst (compose_subst subst0 subst) binding_subst in
              let binding_typ = apply_subst_typ subst_so_far binding_typ in
              (* add new binding type to environment *)
              let new_env = StringMap.add name binding_typ env in
                  (new_env, subst_so_far)
            | BTuple(binds, _) ->  
              let (subst, typ, expr, env') = infer_tuple (bind, expr, loc') env in
              (env', subst) 
        )
        (env, []) bindings 
    in
    let (body_subst, body_typ, aexpr) = infer_exp' funenv new_env aexpr reasons in
    let subst_so_far = compose_subst binds_subst body_subst in
    let body_typ = apply_subst_typ subst_so_far body_typ in
    (subst_so_far, body_typ, e, new_env)
  
  | ESeq(e1, e2, loc) ->
    let (_, _) = infer_exp funenv env sub e1 reasons in
    infer_exp funenv env sub e2 reasons in

  | ETuple(exprs, loc) ->
        let (env, subst, typs) =
          List.fold_left 
          (fun (env, subst, typs) expr -> 
                (* type the expression *)
                let (expr_subst, expr_typ, expr, env') = infer_exp tyenv funenv env expr reasons in
                let subst_so_far = compose_subst expr_subst subst in
                let env = apply_subst_env subst_so_far env' in
                let expr_typ = apply_subst_typ subst_so_far expr_typ in
                (env, subst_so_far, typs @ [expr_typ])
          )
          (env, [], []) exprs 
        in (subst, TyTup(typs, loc), e, env)

  | EGetItem(expr, a, b, loc) -> 
    let (_, tuple_typ, _) = infer_exp' funenv env expr reasons in
      begin match tuple_typ with
            | TyTup(typs, _) -> 
              ([], List.nth typs a, e, env)
            | _ -> ([], tuple_typ, e, env)
      end
  | ESetItem(expr1, a, b, expr2, loc) ->
    let (_, tuple_typ, _) = infer_exp' funenv env expr1 reasons in
      begin match tuple_typ with
            | TyTup(typs, loc) -> 
              let typ = List.nth typs a in
              let typ = unblank typ in
              let (expr2_subst, expr2_typ, expr2) = infer_exp' funenv env expr2 reasons in
              let subst0 = unify tyenv expr2_typ typ loc reasons in 
              
              let subst_so_far = compose_subst subst0 expr2_subst in
              let typ = apply_subst_typ subst_so_far typ in
              ([], typ, e, env)
            | _ -> ([], tuple_typ, e, env)
      end

  | EPrim1(op, expr, loc)         -> infer_app e
  | EPrim2(op, expr1, expr2, loc) -> infer_app e
  | EApp(fun_name, args, loc)     -> infer_app e

  | EAnnot(expr, typ, loc) -> failwith "EAnnot: Finish implementing inferring types for expressions"
  | EIf(c, t, f, loc) ->
    let (c_subst, c_typ, c) = infer_exp' funenv env c reasons in
    let env = apply_subst_env c_subst env in
    let (t_subst, t_typ, t) = infer_exp' funenv env t reasons in
    let env = apply_subst_env t_subst env in
    let (f_subst, f_typ, f) = infer_exp' funenv env f reasons in
    (* Compose the substitutions together *)
    let subst_so_far = compose_subst (compose_subst c_subst t_subst) f_subst in
    (* rewrite the types *)
    let c_typ = apply_subst_typ subst_so_far c_typ in
    let t_typ = apply_subst_typ subst_so_far t_typ in
    let f_typ = apply_subst_typ subst_so_far f_typ in
    (* unify condition with Bool *)
    let unif_subst1 = unify tyenv c_typ tBool loc reasons in
    (* unify two branches *)
    let unif_subst2 = unify tyenv t_typ f_typ loc reasons in
    (* compose all substitutions *)
    let final_subst = compose_subst (compose_subst subst_so_far unif_subst1) unif_subst2 in
    let final_typ = apply_subst_typ final_subst t_typ in
    (final_subst, final_typ, e, env)
  
  | ENil _ -> (sub, tNil)
;;

let infer_decl tyenv funenv env (decl : sourcespan decl) reasons : sourcespan scheme envt * sourcespan typ * sourcespan decl =
  match decl with
  | DFun(f_name, arg_binds, scheme, b, loc) ->

     (* 1. type the arguments and return value. Create fresh type variables for arguments if there
         are no type annotations *)
      (*let () = Printf.printf ";scheme of %s (before typed): %s\n" f_name (string_of_scheme scheme); in*)
      let scheme = match StringMap.find_opt f_name funenv with
                  | Some(scheme') -> scheme' (* in case that the scheme has been instantiated before *)
                  | None    -> scheme 
      in
      let f_typ = instantiate scheme in
     (* 2. add the type of the arguments to the variable environment and type the body *)
      let (arg_typs, ret_typ) = 
        match f_typ with
        | TyArr(arg_typs, ret_typ, _) -> (arg_typs, ret_typ)
        | _ -> failwith "infer_decl: impossible type" 
      in
      let rec build_env env arg_binds arg_typs = 
            List.fold_left2 
            (fun env arg_bind arg_typ ->
              match arg_bind with
            | BBlank(typ, _) -> env (* TODO *)
            | BName(arg_name, typ, _) -> StringMap.add arg_name arg_typ env
            | BTuple(binds, _) -> 
                begin match arg_typ with
                | TyTup(typs, _) -> List.fold_left (fun env bind -> build_env env binds typs) env binds
                | _ -> failwith "build_env: impossible type"
                end
            ) 
            env arg_binds arg_typs 
      in  
      let new_env = build_env env arg_binds arg_typs
      in
     (* 3. type the function body *)
      let (b_subst, b_typ, b, _) = infer_exp tyenv funenv new_env b reasons in
     (* 4. unify the type of function body with type of the function definition *)
      let ret_typ = apply_subst_typ b_subst ret_typ in
      let unif_subst = unify tyenv b_typ ret_typ loc reasons in
      let final_subst = compose_subst b_subst unif_subst in
      let f_typ = apply_subst_typ final_subst f_typ in
      let funenv = apply_subst_funenv final_subst funenv in
     (* 5. generalize the type of the function to type sheme *)
      let scheme = generalize env f_typ in
      (*let () = Printf.printf ";scheme of %s (after typed): %s\n" f_name (string_of_scheme scheme); in*)

      (StringMap.add f_name scheme funenv, f_typ, decl)
;;

(* infer_group: inter types for function gourps that may be mutually recursive *)
let infer_group tyenv funenv env (g : sourcespan decl list) : (sourcespan scheme envt * sourcespan decl list) =
  (* 1. first pull out the scheme of all functions in the group *)
    let funenv = 
      List.fold_left
      (fun funenv decl ->
        match decl with
        | DFun(f_name, arg_names, scheme, b, loc) -> 
            StringMap.add f_name scheme funenv
      ) funenv g
    in
  (* 2. type the body of each function *)
    let (funenv, f_typs) =
      List.fold_left 
      (fun (funenv, f_typs) (DFun(f_name, _, _, _, _) as decl) -> 
         let (funenv', f_typ, _) = infer_decl tyenv funenv env decl [] in
             (funenv', (f_name, f_typ)::f_typs)
      ) (funenv, []) g
    in
  (* 3. generalize the scheme of all functions *)
    let funenv = 
      List.fold_left
      (fun funenv (f_name, f_typ) ->
        StringMap.add f_name (generalize env f_typ) funenv
      ) funenv f_typs
    in
    (funenv, g)
;;

let infer_prog funenv env (p : sourcespan program) : ('a typ * sourcespan program) =
  match p with
  | Program(typedecls, declgroups, body, tag) ->
      (* 1. process typedecls, add type aliases to tyenv *)
      let tyenv =   
        List.fold_left
        (fun tyenv typedecl -> 
          match typedecl with
          | TyDecl(tyname, typs, loc) ->
              StringMap.add tyname (TyTup(typs, loc)) tyenv
        ) StringMap.empty typedecls
      in
      (* 2. type the declgroups *)
      let funenv = 
        List.fold_left 
        (fun funenv g ->
          let (funenv', _) = infer_group tyenv funenv env g in
            funenv'
        ) funenv declgroups
      in
      (* 3. type the body *)
      let (unification, ret_typ, rebuilt_expr, _) = infer_exp tyenv funenv env body [] 
      in 
        (ret_typ, p)
;;

let type_synth (p : sourcespan program) : sourcespan program fallible =
  try
    let (_, p) = infer_prog initial_env StringMap.empty p in Ok(p)
  with e -> Error([e]) 
;;
