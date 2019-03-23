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
let mk_tyarr left right : 'a typ = 
    TyArr(left, right, dummy_span)
;;

let tInt = TyCon("Int", dummy_span)
let tBool = TyCon("Bool", dummy_span)
let tNil = TyCon("Nil", dummy_span)

let tyVarX = TyVar("X", dummy_span)
let tyVarY = TyVar("Y", dummy_span)
(* forall () -> Int *)
let unit2int = SForall([], mk_tyarr [] tInt, dummy_span)
(* forall X, X -> Bool *)
let any2bool = SForall(["X"], mk_tyarr [tyVarX] tBool, dummy_span)
(* forall X Y, X -> Y *)
let any2any = SForall(["X";"Y"], mk_tyarr [tyVarX] tyVarY, dummy_span)
(* forall X Y, X Y -> Bool *)
let anyany2bool = SForall(["X";"Y"], mk_tyarr [tyVarX; tyVarY] tBool, dummy_span)
(*  forall,  Int * Int -> Bool *)
let intint2bool = SForall([], mk_tyarr [tInt; tInt] tBool, dummy_span)
(*  forall,  Bool -> Bool *)
let bool2bool = SForall([], mk_tyarr [tBool] tBool, dummy_span)
(*  forall,  Bool * Bool -> Bool *)
let boolbool2bool = SForall([], mk_tyarr [tBool; tBool] tBool, dummy_span)
(*  forall,  Int -> Int *)
let int2int = SForall([], mk_tyarr [tInt] tInt, dummy_span)
(*  forall,  Int * Int -> Int *)
let intint2int = SForall([], mk_tyarr [tInt; tInt] tInt, dummy_span)

(* initial function environment *)
let initial_env : sourcespan scheme envt =
  List.fold_left (fun env (name, typ) -> StringMap.add name typ env) StringMap.empty [

      (* built-in functions *)
      ("input", unit2int);
      ("print", any2any);
      ("equals", anyany2bool);

      (* prim1 functions *)      
      ("Add1", int2int);
      ("Sub1", int2int);
      ("PrintStack", any2any);
      ("Not",    bool2bool);
      ("IsNum",  any2bool);
      ("IsBool", any2bool);
      ("IsTuple", any2bool);

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

(* free type variables of a type as the set of any type variables that appear within it *)
let rec ftv_type (t : 'a typ) : StringSet.t =
  match t with
  | TyBlank _ -> StringSet.empty
  | TyCon(name, _) -> StringSet.singleton name
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

exception OccursCheck of string
let occurs (name : string) (t : 'a typ) =
  StringSet.mem name (ftv_type t)
;;


(* find_pos: find type of vairable from environment, or find type scheme of function from funenv *)
let rec find_pos (ls : 'a envt) x pos : 'a =
  try
    StringMap.find x ls
  with
  | Not_found -> failwith (sprintf "inference.ml: type of variable %s not found at %s" x (string_of_sourcespan pos))
;;


(* subst_var_typ: converts each occurrence of the given type variable tyvar 
    or type constant (for type alias)
    into the desired type to_typ in the target type in_typ *)
let rec subst_var_typ (((tyvar : string), (to_typ : 'a typ)) as sub) (in_typ : 'a typ): 'a typ =
  match in_typ with 
  | TyBlank _ -> in_typ 
  | TyCon(id, _) -> in_typ
  | TyVar(tyvar1, _) ->
      if String.equal tyvar tyvar1 then to_typ
      else in_typ
  | TyArr(typs, typ, tag) ->
    let typs_subst = List.map (fun typ -> subst_var_typ sub typ) typs in
    let typ_subst = subst_var_typ sub typ in
        TyArr(typs_subst, typ_subst, tag)
  | TyApp(typ, typs, _) -> failwith "subst_var_typ: TyApp not implemented" 
  | TyTup(typs, tag) -> 
    let typs_subst = List.map (fun typ -> subst_var_typ sub typ) typs in
      TyTup(typs_subst, tag)
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


let resolve_alias sub (t : 'a typ)  : 'a typ = 
  match t with
  | TyCon(id, loc) -> 
    begin try 
      let (_, t) = List.find (fun (x, _) -> String.equal x id) sub in t
    with Not_found -> failwith ("resolve_alias: cannot resolve alias" ^ id) 
    end
  | _ -> failwith ("resolve_alias: cannot resolve alias" ^ (string_of_typ t))
;;



let newTyVar (lable: string) loc : 'a typ =
  TyVar(gensym lable, loc)
;;
(* unify:
   given two types t1 and t2, and a pre-existing substitution sub,
   returns the most general substitution sub' which extends sub 
   and makes two given types equal
*)

let rec unify (t1 : 'a typ) (t2 : 'a typ) (sub : 'a typ subst) (loc : sourcespan) (reasons : reason list) : 'a typ subst =  
    let helper t1 t2 : bool = 
      match (t1, t2) with
      | (TyCon(id1, _), TyCon(id2, _)) when (String.equal id1 id2) -> true
      | _ -> false
    in
    (*let () = Printf.printf ";unify of %s -  %s\n" (string_of_typ t1) (string_of_typ t2) in*)
    if (helper t1 t2) then sub else

    let t1 = apply_subst_typ sub t1 in
    let t2 = apply_subst_typ sub t2 in
    match (t1, t2) with 
    | (TyVar(id1, _), TyVar(id2, _)) when (String.equal id1 id2) -> sub
    | (TyVar(id1, _), t2) when not (occurs id1 t2) -> (* extend sub *) compose_subst [(id1, t2)] sub
    | (_, TyVar(id2, _)) -> unify t2 t1 sub loc reasons
    | (TyArr(typs1, typ1, loc1), TyArr(typs2, typ2, loc2)) -> 
        (* unify argument types *)
        let sub = unify (TyTup(typs1, loc1)) (TyTup(typs2, loc2)) sub loc reasons in 
        (* unify the return type *)
        unify typ1 typ2 sub loc reasons 
    | (TyTup(typs1, _), TyTup(typs2, _)) when List.length typs1 == List.length typs2 -> 
        (* unify tuple element types *)
        List.fold_left2
            (fun sub t1 t2 -> unify t1 t2 sub loc reasons)
            sub typs1 typs2 
    | (TyCon(id1, _), TyCon(id2, _)) when (String.equal id1 id2) -> sub

    | (TyCon(id1, loc'), TyTup(_, _)) -> 
    begin
      try
        let t1' = resolve_alias sub t1 in 
            unify t1' t2 sub loc reasons
      with _ -> raise (TypeMismatch(loc, t2, t1, reasons))
    end
    | (TyTup(_, _), TyCon(_, _)) -> unify t2 t1 sub loc reasons

    | _ -> raise (TypeMismatch(loc, t2, t1, reasons))
;;     
     

(* Eliminates all `TyBlank`s in a type, and replaces them with fresh type variables *)
let rec unblank (t : 'a typ) : 'a typ =
  match t with
  | TyBlank tag -> 
      (* create fresh type variable *)
      newTyVar "blank" tag
  | TyCon _ -> t
  | TyVar _ -> t
  | TyArr(args, ret, tag) ->
    let ret = unblank ret in
    let args = List.map unblank args in TyArr(args, ret, tag)
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
        let tyvar = newTyVar "fun" loc in
          (var, tyvar)::subst
      ) [] vars
    in
    apply_subst_typ subst typ
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
    | TyTup(typs, _) -> List.fold_left generalize_typ (env, some) typs
    | TyArr _   -> failwith "generalize_typ: TyArr not implemented - higher order function is not implemented"
    | TyBlank _ -> failwith "generalize_typ: TyBlank - should unblank first"
    | TyApp _   -> failwith "generalize_typ: TyApp - impossible case"
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
          (s  : 'a typ subst) 
          reasons
        : sourcespan typ subst =
  (* infer_app: infer type of function call, including primitive function calls *)
  let infer_app (t : 'a typ) (e : 'a expr): sourcespan typ subst =
      let (fun_name, args, loc') =
         match e with
         | EPrim1(op, expr, loc') -> (name_of_op1 op, [expr], loc')
         | EPrim2(op, expr1, expr2, loc') -> (name_of_op2 op, [expr1; expr2], loc') 
         | _ -> failwith "infer_app: impossible case"
      in
      (* lookup function scheme from funenv *)
      let scheme = find_pos funenv fun_name loc'
      in
      (* fun_ty: generate type of the function *)
      let fun_ty = instantiate scheme in
      match fun_ty with
      | TyArr(typs, typ, _) -> 
        (* type the arguments *)
        let s1 = 
           List.fold_left2 
           (fun s typ arg -> 
              infer_exp funenv env typ arg s reasons 
           ) s typs args 
        in
        (* unify the return type *)
        (unify typ t s1 loc' reasons)
      | _ -> failwith "infer_app: impossible type"
  in
  (*let () = Printf.printf ";infer_exp of %s -  %s\n" (string_of_expr e) (string_of_typ t) in*)
  match e with
  | ENil(typ, loc)  -> unify typ t s loc reasons
  | ENumber(v, loc) -> unify tInt t s loc reasons
  | EBool(v, loc)   -> unify tBool t s loc reasons
  | EId(x, loc)     -> let a = find_pos env x loc in
                       unify a t s loc reasons
  | ELet(args, e2, loc) -> 
    let rec extract_binds env (binds : 'a bind list) : (sourcespan typ envt * 'a typ list) = 
        List.fold_left
        (fun (env, arg_typs) bind ->
          match bind with
        | BName(name, typ, _) -> 
            (* generate a fresh type for typ, if it is blank *)
            let a = unblank typ in
            let env = StringMap.add name a env in
            (env, arg_typs @ [a])
        | BTuple(binds, loc) -> 
            let (env, typs) = extract_binds env binds in
            (env, arg_typs @ [TyTup(typs, loc)])
        | BBlank(typ, _) -> 
            (env, arg_typs @ [(unblank typ)])
        ) 
        (env, []) binds 
    in  
    let (env, arg_typs) = extract_binds env (List.map (fun (x, _, _) -> x) args) in
    let s = 
      List.fold_left2
      (fun s (bind, e, _) t -> 
        infer_exp funenv (apply_subst_env s env) t e s reasons
      ) s args arg_typs
    in
      (* type the body *)
      infer_exp funenv (apply_subst_env s env) t e2 s reasons

  | ESeq(e1, e2, loc) ->
    let a = newTyVar "blank" loc in
    let _ = infer_exp funenv env a e1 s reasons in
      infer_exp funenv env t e2 s reasons
  | ETuple(exprs, loc) ->       
    let (s', t_typs) =
      List.fold_left 
      (fun (s, t_typs) expr ->
          let a = newTyVar "tuple_element" loc in
          let s = infer_exp funenv env a expr s reasons in
          (s, t_typs @ [(apply_subst_typ s a)])         
      ) (s, []) exprs
    in
      unify t (TyTup(t_typs, loc)) s' loc reasons

  | EGetItem(expr, m, n, loc) -> 
    let a = newTyVar "tuple" loc in
    let s = infer_exp funenv env a expr s reasons in
    let a = apply_subst_typ s a in
    let a = 
      try 
        resolve_alias s a  
      with _ -> a 
    in
    begin match a with
          | TyTup(typs, _) -> 
              unify (List.nth typs m) t s loc reasons
          | _ -> failwith ("infer_exp: EGetItem impossible type - not a tuple" ^ (string_of_typ a) ^ (string_of_sourcespan loc))
    end
  | ESetItem(expr1, m, n, expr2, loc) ->
    let s = infer_exp funenv env t expr1 s reasons in
    let a = apply_subst_typ s t in
    begin match a with
          | TyTup(typs, _) -> 
              let b = newTyVar "blank" loc in
              let s1 = infer_exp funenv env b expr2 s reasons in
              let b = apply_subst_typ s1 b in
                unify b (List.nth typs m) s1 loc reasons
          | _ -> failwith ("infer_exp: ESetItem impossible type - not a tuple" ^ (string_of_typ a) ^ (string_of_sourcespan loc))
    end
  | EAnnot(expr, typ, loc) -> infer_exp funenv env typ expr s reasons
  | EIf(c_expr, t_expr, f_expr, loc) ->
    let s = infer_exp funenv env tBool c_expr s reasons in
    let s = infer_exp funenv env t t_expr s reasons in
        infer_exp funenv env t f_expr s reasons


  | EPrim1(op, expr, loc)         -> infer_app t e
  | EPrim2(op, expr1, expr2, loc) -> infer_app t e
  | EApp(f, args, loc) -> 
      let a = List.map (fun _ -> newTyVar "app_arg" loc) args in
      let s1 = infer_exp funenv env (TyArr(a, t, loc)) f s reasons in
          infer_exp funenv env (TyTup(a, loc)) (ETuple(args, loc)) s1 reasons
  
  | ELambda(arg_binds, e, loc) -> 
    let rec bind_to_typs (bind : 'a bind) : 'a typ list = 
        match bind with
        | BBlank(typ, loc) -> [typ]
        | BName(arg_name, typ, loc) -> [typ]
        | BTuple(binds, loc) -> List.map (fun x -> TyTup(bind_to_typs x, loc)) binds
      
    and binds_to_typs (binds : 'a bind list) : 'a typ list = 
        List.concat @@ List.map bind_to_typs binds
    in
    let rec bind_to_env (bind : 'a bind) : 'a typ envt = 
        match bind with
        | BBlank(typ, loc) -> StringMap.empty
        | BName(arg_name, typ, loc) -> StringMap.add arg_name (unblank typ) (StringMap.empty)
        | BTuple(binds, loc) -> binds_to_env binds StringMap.empty
    
    and binds_to_env (binds : 'a bind list) (env : 'a typ envt) : 'a typ envt =
        List.fold_left (fun env bind -> 
                        StringMap.union (fun x y -> failwith "binds_to_env: impossible case") 
                                        env (bind_to_env bind))
        env binds
    in
        (* type the lambda *)
        let arg_typs = binds_to_typs arg_binds in
        let arg_typs = List.map unblank arg_typs in
        let b = newTyVar "lambda_ret" loc in
        let s1 = unify (TyArr(arg_typs, b, loc)) t s loc reasons in

        let lambda_env = binds_to_env arg_binds env in
        let lambda_env = apply_subst_env s1 lambda_env in
        infer_exp funenv lambda_env b e s1 reasons
;;

(* infer_decl: similar to infer_exp *)
let infer_decl funenv env (t : 'a typ) (decl : sourcespan decl)  (s : 'a typ subst) reasons : sourcespan typ subst =
  failwith "infer_decl: should be desugared away"


(* infer_group: inter types for function gourps that may be mutually recursive *)
let infer_group funenv env (g : sourcespan decl list) (s : 'a typ subst) 
  : sourcespan scheme envt =
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
    let f_typs =
      List.fold_left 
      (fun f_typs (DFun(f_name, _, _, _, _) as decl) -> 
        
        let scheme = match StringMap.find_opt f_name funenv with
            | Some(scheme') -> scheme' (* in case that the scheme has been instantiated before *)
            | None    -> failwith "infer_group: undefined function" 
        in
        let f_typ = instantiate scheme in

        let s' = infer_decl funenv env f_typ decl s [] in
             (f_name, apply_subst_typ s' f_typ)::f_typs
      ) [] g
    in
  (* 3. generalize the scheme of all functions *)
    let funenv = 
      List.fold_left
      (fun funenv (f_name, f_typ) ->
        StringMap.add f_name (generalize env f_typ) funenv
      ) funenv f_typs
    in
    funenv
;;

let infer_prog funenv env (p : sourcespan program) : 'a typ =
  match p with
  | Program(typedecls, declgroups, body, tag) ->
      (* 1. process typedecls, add type aliases to substitution s *)
      let s =
        List.fold_left
        (fun s typedecl -> 
          match typedecl with
          | TyDecl(tyname, typs, loc) ->
              let b = TyTup(typs, loc) in
              compose_subst [(tyname, b)] s
        ) [] typedecls
      in
      (* 2. type the declgroups *)
      let funenv = 
        List.fold_left 
        (fun funenv (g : sourcespan decl list) ->
                infer_group funenv env g s
        ) funenv declgroups
      in
      (* 3. type the body *)
      let a = TyVar(gensym "body", tag) in
      let s = infer_exp funenv env a body s [] in 
        apply_subst_typ s a
;;

let type_synth (p : sourcespan program) : sourcespan program fallible =
  try
    let _ = infer_prog initial_env StringMap.empty p in
(*    let () = Printf.printf ";type_synth %s\n" (string_of_typ t) in
*)     Ok(p)
  with e -> Error([e]) 
;;
