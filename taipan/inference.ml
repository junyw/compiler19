open Exprs
open Errors
open Printf
open Pretty
open Phases

module StringMap = Map.Make(String);;
module StringSet = Set.Make(String);;

type 'a envt = 'a StringMap.t;;
type 'a subst = (string * 'a) list;;

let print_funenv funenv =
  StringMap.iter (fun name scheme -> debug_printf "\t%s => %s\n" name (string_of_scheme scheme)) funenv;;
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

let rec find_pos (ls : 'a envt) x pos : 'a =
  try
    StringMap.find x ls
  with
  | Not_found -> failwith (sprintf "Name %s not found at %s" x (string_of_sourcespan pos))
;;


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
;;
let ftv_scheme (s : 'a scheme) : StringSet.t =
  match s with
  | SForall(args, typ, _) ->
     StringSet.diff (ftv_type typ) (StringSet.of_list args)
let ftv_env (e : 'a typ envt) : StringSet.t = 
  failwith "Compute the free type variables of an environment here"
;;
let occurs (name : string) (t : 'a typ) =
  StringSet.mem name (ftv_type t)
;;
exception OccursCheck of string
let bind (tyvarname : string) (t : 'a typ) : 'a typ subst =
  match t with
  | TyVar(name, _) when tyvarname = name -> [] (* nothing to be done *)
  | _ ->
     if StringSet.mem tyvarname (ftv_type t)
     then raise (OccursCheck (sprintf "Infinite types: %s occurs in %s" tyvarname (string_of_typ t)))
     else [(tyvarname, t)]
;;
let ty_err t1 t2 loc reasons = TypeMismatch(loc, t2, t1, reasons)


let rec unify (t1 : 'a typ) (t2 : 'a typ) (loc : sourcespan) (reasons : reason list) : 'a typ subst =
  let is_same_typ_var t1 t2 = match t1 with
    | TyVar(id1, _) -> 
      begin match t2 with 
            | TyVar(id2, _) -> String.equal id1 id2
            | _ -> false
      end
    | TyCon(id1, _) ->
        begin match t2 with 
                | TyCon(id2, _) -> String.equal id1 id2
                | _ -> false
        end
    | _ -> false 
  in
  if is_same_typ_var t1 t2 then []
  else 
    match t1 with 
    | TyVar(id1, _) when not (occurs id1 t2) -> 
       [(id1, t2)]
    | TyArr(typs, typ, _) -> 
     begin match t2 with  
          | TyArr(typs2, typ2, _) -> 
            (* unify argument types *)
            let subst1 = 
                List.fold_left2
                (fun subst typ typ2 -> 
                    let subst0 = unify typ typ2 loc reasons in
                        compose_subst subst subst0)
                [] typs typs2 
            in
            (* unify the return type *)
            let typ = apply_subst_typ subst1 typ in
            let typ2 = apply_subst_typ subst1 typ2 in
			   		let subst2 = unify typ typ2 loc reasons in
			   		compose_subst subst2 subst1
			   | _ -> raise (TypeMismatch(loc, t2, t1, reasons))
	     end
    | _ -> 
      begin match t2 with 
            | TyVar(id2, _) when not (occurs id2 t1) ->
		 			     [(id2, t1)]
            | _ -> raise (TypeMismatch(loc, t2, t1, reasons))
      end
;;     
     
let gensym =
  let count = ref 0 in
  let next () =
    count := !count + 1;
    !count
  in fun str -> sprintf "%s_%d" str (next ());;

(* Eliminates all `TyBlank`s in a type, and replaces them with fresh type variables *)
let rec unblank (t : 'a typ) : 'a typ =
  match t with
  | TyBlank tag -> TyVar(gensym "blank", tag)
  | TyCon _ -> t
  | TyVar _ -> t
  | TyArr(args, ret, tag) ->
     let args = List.map unblank args in
     let ret = unblank ret in TyArr(args, ret, tag)
  | TyApp(t, args, tag) ->
     let t = unblank t in
     let args = List.map unblank args in TyApp(t, args, tag)
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
  let generalize_typ (env, (some : string list)) (t : 'a typ) = 
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


let rec infer_exp (funenv : sourcespan scheme envt) (env : sourcespan typ envt) (e : sourcespan expr) reasons
        : (sourcespan typ subst * sourcespan typ * sourcespan expr) (* unification, result typ, rebuilt expr *)=
  (* infer_app: infer type of function call, including primitive function calls *)
  let infer_app (e : 'a expr)  
        : (sourcespan typ subst * sourcespan typ * sourcespan expr) =
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
      (* type of the arguments *)
      let (arg_substs, args_typs) = 
         List.fold_left 
         (fun (subst_so_far, args_typs) arg -> 
            let (arg_subst, arg_typ, arg) = infer_exp funenv env arg reasons in 
            (compose_subst arg_subst subst_so_far, args_typs@[arg_typ])
         ) ([], []) args
      in
      (* type of the function call *)
      let app_typ = TyArr(args_typs, ret_ty, loc) in
      let app_typ = apply_subst_typ arg_substs app_typ in
      (* unification *)
      let unif_subst1 = unify app_typ fun_ty loc reasons in
      let final_subst = compose_subst unif_subst1 arg_substs in
      let final_typ = apply_subst_typ final_subst ret_ty in
      (final_subst, final_typ, e)   
  in

  match e with
  | ENumber(v, loc) -> ([], tInt, e)
  | EBool(v, loc) -> ([], tBool, e)
  | EId(x, loc) ->  ([], find_pos env x loc, e)
  | ELet(binds, aexpr, loc) -> 
    let (new_env, binds_subst) = 
        List.fold_left 
        (fun (env, subst) (typbind, expr, loc') -> 
            (* type the binding *)
            let (binding_subst, binding_typ, expr) = infer_exp funenv env expr reasons in
            (* typ is the user provided type annotation, maybe blank *)
            let (name, typ, _) = typbind in
            let typ = unblank typ in
            (* unification *)
            let subst0 = unify binding_typ typ loc' reasons in 
            let subst_so_far = compose_subst (compose_subst subst0 subst) binding_subst in
            let binding_typ = apply_subst_typ subst_so_far binding_typ in
            (* add new binding type to environment *)
            let new_env = StringMap.add name binding_typ env in
                (new_env, subst_so_far))
        (env, []) binds 
    in
    let (body_subst, body_typ, aexpr) = infer_exp funenv new_env aexpr reasons in
    let subst_so_far = compose_subst binds_subst body_subst in
    let body_typ = apply_subst_typ subst_so_far body_typ in
    (subst_so_far, body_typ, e)

  | EPrim1(op, expr, loc)         -> infer_app e
  | EPrim2(op, expr1, expr2, loc) -> infer_app e
  | EApp(fun_name, args, loc)     -> infer_app e
  | EAnnot(expr, typ, loc) -> failwith "EAnnot: Finish implementing inferring types for expressions"
  | EIf(c, t, f, loc) ->
     let (c_subst, c_typ, c) = infer_exp funenv env c reasons in
     let env = apply_subst_env c_subst env in
     let (t_subst, t_typ, t) = infer_exp funenv env t reasons in
     let env = apply_subst_env t_subst env in
     let (f_subst, f_typ, f) = infer_exp funenv env f reasons in
     (* Compose the substitutions together *)
     let subst_so_far = compose_subst (compose_subst c_subst t_subst) f_subst in
     (* rewrite the types *)
     let c_typ = apply_subst_typ subst_so_far c_typ in
     let t_typ = apply_subst_typ subst_so_far t_typ in
     let f_typ = apply_subst_typ subst_so_far f_typ in
     (* unify condition with Bool *)
     let unif_subst1 = unify c_typ tBool loc reasons in
     (* unify two branches *)
     let unif_subst2 = unify t_typ f_typ loc reasons in
     (* compose all substitutions *)
     let final_subst = compose_subst (compose_subst subst_so_far unif_subst1) unif_subst2 in
     let final_typ = apply_subst_typ final_subst t_typ in
     (final_subst, final_typ, e)
;;

let infer_decl funenv env (decl : sourcespan decl) reasons : sourcespan scheme envt * sourcespan typ * sourcespan decl =
  match decl with
  | DFun(f_name, arg_names, scheme, b, loc) ->
     (* 1. type the arguments and return value. Create fresh type variables for arguments if there
         are no type annotations *)
      let () = Printf.printf ";scheme of %s (before typed): %s\n" f_name (string_of_scheme scheme); in
      let scheme = match StringMap.find_opt f_name funenv with
                  | Some(scheme') -> scheme' (* in case that the scheme has been instantiated before *)
                  | None    -> scheme 
      in
      let f_typ = instantiate scheme in
     (* 2. add the type of the arguments to the type environment and type the body *)
      let (arg_typs, ret_typ) = 
        match f_typ with
        | TyArr(arg_typs, ret_typ, _) -> (arg_typs, ret_typ)
        | _ -> failwith "infer_decl: impossible type" 
      in
      let new_env =
            List.fold_left2 
            (fun env (arg_name, _) arg_typ ->
              StringMap.add arg_name arg_typ env
            ) env arg_names arg_typs 
            (* note: arg_names and arg_typs must have same length, which is assured by well-fromedness check *)
      in
     (* 3. type the function body *)
      let (b_subst, b_typ, b) = infer_exp funenv new_env b reasons in
     (* 4. unify the type of function body with type of the function definition *)
      let ret_typ = apply_subst_typ b_subst ret_typ in
      let unif_subst = unify b_typ ret_typ loc reasons in
      let final_subst = compose_subst b_subst unif_subst in
      let f_typ = apply_subst_typ final_subst f_typ in
      let funenv = apply_subst_funenv final_subst funenv in
     (* 5. generalize the type of the function to type sheme *)
      let scheme = generalize env f_typ in
      let () = Printf.printf ";scheme of %s (after typed): %s\n" f_name (string_of_scheme scheme); in

      (StringMap.add f_name scheme funenv, f_typ, decl)
;;

(* infer_group: inter types for function gourps that may be mutually recursive *)
let infer_group funenv env (g : sourcespan decl list) : (sourcespan scheme envt * sourcespan decl list) =
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
         let (funenv', f_typ, _) = infer_decl funenv env decl [] in
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
  | Program(declgroups, body, typ, tag) ->
      (* 1. type the declgroups *)
      let funenv = 
        List.fold_left 
        (fun funenv g ->
          let (funenv', _) = infer_group funenv env g in
            funenv'
        ) funenv declgroups
      in
      (* 2. type the body *)
      let (unification, ret_typ, rebuilt_expr) = infer_exp funenv env body [] 
      in 
        (ret_typ, p)
;;

let type_synth (p : sourcespan program) : sourcespan program fallible =
  try
    let (_, p) = infer_prog initial_env StringMap.empty p in Ok(p)
  with e -> Error([e])
;;
