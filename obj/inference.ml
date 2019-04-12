open Exprs
open Errors
open Printf
open Pretty
open Phases

(*
Type inference:
Tuple bindings are desguared away before type inference.
*)

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

let print_env env =
  StringMap.iter (fun name scheme -> printf ";\t%s => %s\n" name (string_of_scheme scheme)) env;;
let print_subst subst =
  List.iter (fun (name, typ) -> printf ";\t%s => %s\n" name (string_of_typ typ)) subst;;
let print_set ftv_set =
  StringSet.iter (fun name -> printf ";\t%s \n" name) ftv_set;;

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

(* initial type environment *)
let initial_env : sourcespan scheme envt =
  List.fold_left (fun env (name, scheme) -> StringMap.add name scheme env) StringMap.empty [

      (* predefined functions: TODO *)
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
      ("Print", any2any);

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
  | TyCon(name, _) -> StringSet.empty
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
  | TyRecord(records, tag) ->
    List.fold_right (fun (_, t) ftvs -> StringSet.union (ftv_type t) ftvs)
                   records
                   StringSet.empty
;;
(* ftv_scheme: 
  The set of free type variables of a type scheme is the set of free type variables of its type component, 
  excluding any quantified type variables *)
let ftv_scheme (s : 'a scheme) : StringSet.t =
  match s with
  | SForall(args, typ, _) ->
     StringSet.diff (ftv_type typ) (StringSet.of_list args)

(* ftv_env:
   The set of free type variables of an environment is the union of the free type variables of all type schemes 
   recorded in it *)
let ftv_env (e : 'a scheme envt) : StringSet.t = 
  StringMap.fold
    (fun _ scheme ftvs ->
          StringSet.union (ftv_scheme scheme) ftvs) e StringSet.empty

;;

exception OccursCheck of string
let occurs (name : string) (t : 'a typ) =
  StringSet.mem name (ftv_type t)
;;


(* find_pos: find type of vairable from environment, or find type scheme of function from funenv *)
let rec find_pos (ls : 'scheme envt) x pos : 'scheme =
  let () = Printf.printf ";find_pos: looked up %s\n" x in
  let res = 
    try
      StringMap.find x ls
    with
    | Not_found -> failwith (sprintf "inference.ml: type of variable %s not found at %s" x (string_of_sourcespan pos))
  in
  let () = Printf.printf ";find_pos: looked up %s - %s\n" x (string_of_scheme res) in
    res
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
  | TyRecord(records, tag) ->
      TyRecord(List.map (fun (key, typ) -> (key, subst_var_typ sub typ)) records, tag)
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
let apply_subst_env (subst : 'a typ subst) (env : 'a scheme envt) : 'a scheme envt =
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
    let () = Printf.printf ";unify of %s -  %s\n" (string_of_typ t1) (string_of_typ t2) in
    if (helper t1 t2) then sub else

    let t1 = apply_subst_typ sub t1 in
    let t2 = apply_subst_typ sub t2 in
    let () = Printf.printf ";unify of types after substitution %s - %s\n" (string_of_typ t1) (string_of_typ t2) in

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
    | (TyTup(_, _), TyCon(_, _)) -> 
      unify t2 t1 sub loc reasons

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
  | TyRecord _ -> t
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
    let typ = apply_subst_typ subst typ in
    let () = Printf.printf ";instantiate %s to %s\n" (string_of_scheme s) (string_of_typ typ) in
    typ
;;

let loc_of_typ t = 
  match t with
  | TyBlank(loc) -> loc
  | TyCon(_, loc) -> loc
  | TyVar(_, loc) -> loc 
  | TyArr(_, _, loc) -> loc 
  | TyApp(_, _, loc) -> loc 
  | TyTup(_, loc) -> loc
  | TyRecord(_, loc) -> loc
;;
let loc_of_scheme sch =
  match sch with
  | SForall(_, _, loc) -> loc
;;

let nameof_bind (bind : 'a bind) : string = 
    match bind with 
    | BName(name, _, _) -> name
    | _ -> failwith "infer_class: impossible case - can't find name of the field"
;;
(* generalize: turns a given type into a type scheme, quantifying over all type
   variables that are free in the type, but not in the environment.*)
let rec generalize (e : 'a scheme envt) (t : 'a typ) : 'a scheme =
    match t with
    | _ -> 
      let loc = loc_of_typ t in
      SForall((StringSet.elements @@  StringSet.diff (ftv_type t) (ftv_env e)), t, loc)

let mk_scheme (t : 'a typ) : 'a scheme =
    let loc = loc_of_typ t in
    SForall([], t, loc)


let is_blanktyp (typ : 'a typ) : bool = 
  match typ with
  | TyBlank _ -> true
  | _ -> false
;;

(* tyeqv: check if two types are the same *)
let rec tyeqv env tyS tyT =
  match (tyS, tyT) with
  | (TyBlank(_), TyBlank(_)) -> failwith "tyeqv: blank type"
  | (TyCon(str1, _), TyCon(str2, _)) -> String.equal str1 str2
  | (TyVar(x1, pos), _) ->
      tyeqv env (instantiate (find_pos env x1 pos)) tyT
  | (_, TyVar(x2, pos)) ->
      tyeqv env tyS (instantiate (find_pos env x2 pos))
  | (TyArr(tys1, ty1, _), TyArr(tys2, ty2, _)) ->
    List.for_all2
      (fun ty1 ty2 -> tyeqv env ty1 ty2) tys1 tys2
    &&
    tyeqv env ty1 ty2
  | (TyTup(tys1, _), TyTup(tys2, _)) ->
    List.for_all2
      (fun ty1 ty2 -> tyeqv env ty1 ty2) tys1 tys2
  | (TyRecord(records1, _), TyRecord(records2, _)) ->
      (List.length records1 = List.length records2)
      &&
      List.for_all 
        (fun (r2, ty2) ->
            try let ty1 = List.assoc r2 records1 in
                tyeqv env ty1 ty2
            with Not_found -> false)
        records2
  | (TyApp(ty1, tys1, _), TyApp(ty2, tys2, _)) -> failwith "tyeqv: needs to be implemented"
  | _ -> false
;;

(* typeof_* functions: returns the type, without doing type inference *)
let rec typeof_bind (bind : 'a bind) : 'a typ = 
    match bind with
    | BBlank(typ, loc) -> typ
    | BName(arg_name, typ, loc) -> typ
    | BTuple(binds, loc) -> failwith "typeof_bind: Tuple binding should have been desugared away"
;;
let typeof_literal (lit : 'a expr) : 'a typ = 
  match lit with 
  | ENumber _ -> tInt
  | EBool _ -> tBool
  | _ -> failwith "typeof_literal: not a literal (number of bool)"
;;
(* typeof_field: 
   given a field, returns the type of the field 
   1. if the field is not annotated, returns a blank type
   2. if the field is annotated, without being assigned a value, returns the annotated type
   3. if the field is annotated and is assigned a value, checks the annotation matches with the type of the given value, 
   and returns the type
*)
let typeof_field (field : 'a field) : 'a typ =
  match field with
  | Field(bind, Some(ini), loc) ->
    let inityp = typeof_literal ini in
    let bindtyp = typeof_bind bind in
    if is_blanktyp bindtyp then inityp
    else
      if tyeqv StringMap.empty inityp bindtyp then inityp
      else failwith (sprintf "typeof_field %s: type annot (%s) and initial value (%s) have different type" (nameof_bind bind) (string_of_typ bindtyp) (string_of_expr ini))
  | Field(bind, None, loc) ->
    typeof_bind bind
;;
let schemeof_decls (g : sourcespan decl list) : (string * 'a scheme) list =
    List.fold_left
    (fun assoc decl ->
      match decl with
      | DFun(f_name, arg_names, scheme, b, loc) -> 
          assoc @ [(f_name, scheme)]
    ) [] g
;;


let rec bind_to_typs (bind : 'a bind) : 'a typ list = 
    [(typeof_bind bind)]
and binds_to_typs (binds : 'a bind list) : 'a typ list = 
    List.concat @@ List.map bind_to_typs binds
;;

let rec bind_to_env (bind : 'a bind) s (env : 'a scheme envt) : 'a scheme envt = 
    match bind with
    | BBlank(typ, loc) -> env
    | BName(arg_name, typ, loc) -> StringMap.add arg_name (generalize env (apply_subst_typ s typ)) env
    | BTuple(binds, loc) -> binds_to_env binds s env
and binds_to_env (binds : 'a bind list) s (env : 'a scheme envt) : 'a scheme envt =
    let env = apply_subst_env s env in
    List.fold_left (fun env bind -> 
                    bind_to_env bind s env)
    env binds
;;



(* infer_exp
   env: environment that associate variable names with their type scheme
   t: a proto-type
   e: expression
   s: pre-existing substitution
  
   returns: a new substitution s' that extends s
*)
let rec infer_exp 
          (env : sourcespan scheme envt) 
          (t : 'a typ)
          (e : sourcespan expr) 
          (s  : 'a typ subst) 
          reasons
        : sourcespan typ subst =
  let () = Printf.printf ";infer_exp of %s -  %s\n" (string_of_expr e) (string_of_typ t) in
  (*let () = print_env env in*)
  (*let () = print_subst s in*)
  let result = 
  match e with
  | ENil(typ, loc)  -> unify typ t s loc reasons
  | ENumber(v, loc) -> unify tInt t s loc reasons
  | EBool(v, loc)   -> unify tBool t s loc reasons
  | EId(x, loc)     -> 
      let a = find_pos env x loc in
      let a = instantiate a in
      unify a t s loc reasons
  
  | ELet([], e2, loc) -> infer_exp env t e2 s reasons
  | ELet(((bind : 'a bind), e1, loc')::rest, e2, loc) ->  
    let rec unblank_bind bind = 
      match bind with
      | BBlank(typ, loc) -> BBlank(unblank typ, loc)
      | BName(arg_name, typ, loc) -> BName(arg_name, unblank typ, loc) 
      | BTuple(binds, loc) -> BTuple(List.map unblank_bind binds, loc)
    in
    let bind = unblank_bind bind in
    let a = match bind_to_typs bind with
            | [typ] -> typ
            | _ -> failwith "infer_exp: ELet binding of impossible case" 
    in
    (*let a = unblank a in *)(* should be unblank a bind, so that they maintain the same tyvars *)
    let s1 = infer_exp env a e1 s reasons in
    let env = apply_subst_env s1 env in
    let env' = binds_to_env [bind] s1 env in
      infer_exp env' (apply_subst_typ s1 t) (ELet(rest, e2, loc)) s1 reasons

  | ELetRec _ -> s (* TODO *)

  | ESeq(e1, e2, loc) ->
    let a = newTyVar "blank" loc in
    let _ = infer_exp env a e1 s reasons in
      infer_exp env t e2 s reasons
  
  | ETuple(exprs, loc) ->       
    let (s', t_typs) =
      List.fold_left 
      (fun (s, t_typs) expr ->
          let a = newTyVar "tuple_element" loc in
          let s = infer_exp env a expr s reasons in
          (s, t_typs @ [(apply_subst_typ s a)])         
      ) (s, []) exprs
    in
      unify t (TyTup(t_typs, loc)) s' loc reasons
  | EGetItem(expr, m, n, loc) -> 
    let a = newTyVar "tuple" loc in
    let s = infer_exp env a expr s reasons in
    let a = apply_subst_typ s a in
    let a = 
      try 
        resolve_alias s a  
      with _ -> a 
    in
    begin match a with
          | TyTup(typs, _) -> 
              unify (List.nth typs m) t s loc reasons
          | _ -> failwith ("infer_exp: EGetItem impossible type - not a tuple " ^ (string_of_typ a) ^ " " ^ (string_of_sourcespan loc))
    end
  | ESetItem(expr1, m, n, expr2, loc) ->
    let s = infer_exp env t expr1 s reasons in
    let a = apply_subst_typ s t in
    let a = 
      try 
        resolve_alias s a  
      with _ -> a 
    in
    begin match a with
          | TyTup(typs, _) -> 
              let b = newTyVar "blank" loc in
              let s1 = infer_exp env b expr2 s reasons in
              let b = apply_subst_typ s1 b in
                unify b (List.nth typs m) s1 loc reasons
          | _ -> failwith ("infer_exp: ESetItem impossible type - not a tuple " ^ (string_of_typ a) ^ " " ^ (string_of_sourcespan loc))
    end
  
  | EAnnot(expr, typ, loc) -> 
    let s = unify t (unblank typ) s loc reasons in
    infer_exp env t expr s reasons

  | EIf(c_expr, t_expr, f_expr, loc) ->
    let s = infer_exp env tBool c_expr s reasons in
    let s = infer_exp env t t_expr s reasons in
        infer_exp env t f_expr s reasons


  | EPrim1(op, expr, loc) -> 
      infer_exp env t (EApp(EId(name_of_op1 op, loc), [expr], loc)) s reasons
  | EPrim2(op, expr1, expr2, loc) -> 
      infer_exp env t (EApp(EId(name_of_op2 op, loc), [expr1; expr2], loc)) s reasons
  | EApp(f, args, loc) -> 
      let a = List.map (fun _ -> newTyVar "app_arg" loc) args in
      let s = infer_exp env (TyArr(a, t, loc)) f s reasons in
      let f_ty = apply_subst_typ s (TyArr(a, t, loc)) in
      begin
        match f_ty with
        | TyArr(typs, typ, _) -> 
          (* type the arguments *)
          let s = 
             List.fold_left2 
             (fun s typ arg -> 
                infer_exp env typ arg s reasons 
             ) s typs args 
          in
          (* unify the return type *)
          (unify typ t s loc reasons)
        | _ -> failwith "infer_app: EApp impossible type"
      end

  | ELambda(arg_binds, e, loc) -> 
      (* type the lambda *)
      let arg_typs = binds_to_typs arg_binds in
      let arg_typs = List.map unblank arg_typs in
      let b = newTyVar "lambda_ret" loc in
      let s1 = unify (TyArr(arg_typs, b, loc)) t s loc reasons in

      let lambda_env = binds_to_env arg_binds s env in
      let lambda_env = apply_subst_env s1 lambda_env in
      infer_exp lambda_env b e s1 reasons
 
  | ENew(str, loc) -> 
      let a = find_pos env str loc in
      let a = instantiate a in
      unify a t s loc reasons

  | EDot(expr, str, loc) -> 
      let a = newTyVar "object" loc in
      let s = infer_exp env a expr s reasons in
      let () = Printf.printf "infer_exp EDot %s" (string_of_expr expr) in 
      let () = print_subst s in
      let a = apply_subst_typ s a in
      begin match a with
            | TyRecord(records, _) -> 
                unify (List.assoc str records) t s loc reasons
            | _ -> failwith ("infer_exp: EDot impossible type - not a object " ^ (string_of_expr expr) ^ " " ^ (string_of_typ a) ^ " " ^ (string_of_sourcespan loc))
      end

  | EDotSet(expr1, str, expr2, loc) -> 
      let s = infer_exp env t expr1 s reasons in
      let a = apply_subst_typ s t in
      let b = newTyVar "blank" loc in
      let s1 = infer_exp env b expr2 s reasons in
      let b = apply_subst_typ s1 b in
        unify a b s1 loc reasons
  in
  let () = Printf.printf ";infer_exp generated substitution: \n" in
  let () = print_subst result in
  let () = Printf.printf ";>>infer_exp of %s result - %s\n" (string_of_expr e) (string_of_typ (apply_subst_typ result t)) in
    result
;;

(* infer_decl: similar to infer_exp *)
let infer_decl env (t : 'a typ) (decl : sourcespan decl)  (s : 'a typ subst) reasons : sourcespan typ subst =
  (*  takes the pre-existing environment, a list of binds, a list of types,
      extracts all the variables from binds and add them to the environment, creates new type variable if necessary
      returns the extended environment. *)
  let () = Printf.printf ";infer_decl of %s -  %s\n" (string_of_decl decl) (string_of_typ t) in
  (*let () = print_env env in*)
  match t with
    | TyArr(a, b, _) ->
      begin
      match decl with
      | DFun(f_name, arg_binds, scheme, e, loc) ->
        let env_with_args = 
            List.fold_left2
            (fun env arg_bind arg_ty ->
              let arg_name = nameof_bind arg_bind in
              if String.equal arg_name "self" then env
              else StringMap.add arg_name (SForall([], arg_ty, loc)) env)
            env arg_binds a
        in
        let s = infer_exp env_with_args b e s reasons in
        let () = Printf.printf ";infer_decl type of %s (after typed): %s\n" f_name (string_of_typ (apply_subst_typ s t)) in
        let () = Printf.printf ";infer_decl generated substitution: \n" in
        let () = print_subst s in
        s
      end   
    | _ -> failwith "infer_decl: unexpected type"
;;


(* decls_to_env *)
let decls_to_env env (g : sourcespan decl list) : sourcespan scheme envt =
    List.fold_left
    (fun env decl ->
      match decl with
      | DFun(f_name, arg_names, scheme, b, loc) -> 
          StringMap.add f_name scheme env
    ) env g
;;

(* infer_group: inter types for function groups that may be mutually recursive
   apply the substitutions to the given env and return the new env
 *)
let infer_group env (g : sourcespan decl list) (s : 'a typ subst) 
  : (sourcespan scheme envt * 'a typ subst) =
  (* first pull out the scheme of all functions in the group *)
    let env = decls_to_env env g in
    (*  type the body of each function *)
    let (env, s) =
      List.fold_left 
      (fun (env, s) (DFun(f_name, _, _, _, _) as decl) -> 
        
        let scheme = match StringMap.find_opt f_name env with
            | Some(scheme') -> scheme' 
            | None    -> failwith "infer_group: undefined function" 
        in
        let f_typ = instantiate scheme in

        let s' = infer_decl env f_typ decl s [] in
        let env' = apply_subst_env s' env in
            (StringMap.add f_name (generalize env' (apply_subst_typ s' f_typ)) env', s')
      ) (env, s) g
    in
    let () = Printf.printf ";infer_group: after typing: \n" in
    let () = print_env env in
    let () = print_subst s in
      (env, s)  
;;

let nameof_class (c : 'a classdecl) : string = 
  match c with
  | Class(str, _, _, _, _) -> str
;;

(* infer_class: inter types for classes 
  We use rules similar to https://crystal-lang.org/reference/syntax_and_semantics/type_inference.html
*)
let infer_class env (classdecl : sourcespan classdecl) (s : 'a typ subst) 
  : sourcespan scheme envt = 
  let nameof_field (Field(bind, _, _) : 'a field) : string =
    nameof_bind bind
  in
  match classdecl with
  | Class(c_name, None, fields, classmethods, pos) ->
    let fieldtys =
      List.map (fun field -> (nameof_field field, typeof_field field)) fields 
    in
    let methodschemes = schemeof_decls classmethods in
    let methodtyps = List.map (fun (key, sch) -> (key, (instantiate sch))) methodschemes in
    let self = TyRecord(fieldtys @ methodtyps, pos) in
    let env = StringMap.add "self" (SForall([], self, loc_of_typ self)) env in

    let (env, s) = 
      List.fold_left 
      (fun (env, s) (DFun(f_name, _, _, _, loc') as decl) -> 
        let f_typ = match self with
          | TyRecord(records, _) -> 
            begin match List.assoc_opt f_name records with
            | Some(scheme') -> scheme' 
            | None    -> failwith "infer_class: undefined function" 
            end
          | _ -> failwith "infer_class: impossible case"
        in
        let s' = infer_decl env f_typ decl s [] in
        let env' = apply_subst_env s' env in
            (apply_subst_env s' env', s')
      ) (env, s) classmethods
    in
    let env = apply_subst_env s env in
    let () = Printf.printf ";infer_class: after typing the methods\n" in
    let () = print_subst s in
    let self = apply_subst_typ s self in
    let () = Printf.printf ";infer_class: the type of the class is %s\n" (string_of_typ self) in

    let ftv = ftv_type self in
    let () = Printf.printf ";infer_class: free type vars \n" in
    let () = print_set ftv in
    if not (StringSet.is_empty ftv) then
      failwith (sprintf "infer_class: can not fully type the class - %s" (string_of_typ self))
    else
    let () = Printf.printf ";infer_class %s: %s\n" (nameof_class classdecl) (string_of_typ self) in
    StringMap.add c_name (SForall([], self, loc_of_typ self)) (apply_subst_env s env) 

  | Class(c_name, Some(basename), fields, classmethods, pos) ->
    
    let base_scheme = find_pos env basename pos in
    let base_fields = 
      match instantiate base_scheme with
      | TyRecord(records, _) ->  records
      | _ -> failwith "infer_class: base class impossible type"
    in
    let fieldtys =
      List.map (fun field -> (nameof_field field, typeof_field field)) fields 
    in
    let methodschemes = schemeof_decls classmethods in
    let methodtyps = List.map (fun (key, sch) -> (key, (instantiate sch))) methodschemes in
    (* TODO: handle overriding *)
    let self = TyRecord(base_fields @ fieldtys @ methodtyps, pos) in
    let env = StringMap.add "self" (SForall([], self, loc_of_typ self)) env in

    let (env, s) = 
      List.fold_left 
      (fun (env, s) (DFun(f_name, _, _, _, loc') as decl) -> 
        let f_typ = match self with
          | TyRecord(records, _) -> 
            begin match List.assoc_opt f_name records with
            | Some(scheme') -> scheme' 
            | None    -> failwith "infer_class: undefined function" 
            end
          | _ -> failwith "infer_class: impossible case"
        in
        let s' = infer_decl env f_typ decl s [] in
        let env' = apply_subst_env s' env in
            (apply_subst_env s' env', s')
      ) (env, s) classmethods
    in
    let env = apply_subst_env s env in
    let () = Printf.printf ";infer_class: after typing the methods\n" in
    let () = print_subst s in
    let self = apply_subst_typ s self in
    let () = Printf.printf ";infer_class: the type of the class is %s\n" (string_of_typ self) in

    let ftv = ftv_type self in
    let () = Printf.printf ";infer_class: free type vars \n" in
    let () = print_set ftv in
    if not (StringSet.is_empty ftv) then
      failwith (sprintf "infer_class: can not fully type the class - %s" (string_of_typ self))
    else
    let () = Printf.printf ";infer_class %s: %s\n" (nameof_class classdecl) (string_of_typ self) in
    StringMap.add c_name (SForall([], self, loc_of_typ self)) (apply_subst_env s env) 
;;

let infer_prog env (p : sourcespan program) : 'a typ =
  match p with
  | Program(typedecls, classdecls, declgroups, body, tag) ->
      (* process typedecls, add type aliases to substitution s *)
      let s =
        List.fold_left
        (fun s typedecl -> 
          match typedecl with
          | TyDecl(tyname, typs, loc) ->
              let b = TyTup(typs, loc) in
              compose_subst [(tyname, b)] s
        ) [] typedecls
      in
      (* type the classes *)
      let env = 
        List.fold_left 
        (fun env (c : sourcespan classdecl) ->
          infer_class env c s
        ) env classdecls
      in
      (* type the declgroups *)
      let env = 
        List.fold_left 
        (fun env (g : sourcespan decl list) ->
                let (env, _) = infer_group env g s in env
        ) env declgroups
      in
      (* 3. type the body *)
      let a = TyVar(gensym "body", tag) in
      let s = infer_exp env a body s [] in 
      let ret_typ =  apply_subst_typ s a in
      let () = Printf.printf ";type_prog: ret type %s\n" (string_of_typ ret_typ) in
      let () = Printf.printf ";type_prog: final env\n" in
      let () = print_env env in

      ret_typ
;;

let type_synth (p : sourcespan program) : sourcespan program fallible =
  try
    let _ = infer_prog initial_env p in
    (* let () = Printf.printf ";type_synth %s\n" (string_of_typ t) in *)
     Ok(p)
  with e -> Error([e]) 
;;
