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

(*  forall,  Int * Int -> Int *)
let intint2int = SForall([], mk_tyarr [tInt; tInt] tInt, dummy_span)

(*  forall,  Int -> Int *)
let int2int = SForall([], mk_tyarr [tInt] tInt, dummy_span)

(*  forall,  Int -> Bool *)
let int2bool = SForall([], mk_tyarr [tInt] tBool, dummy_span)
let tyVarX = TyVar("X", dummy_span)
let any2bool = SForall(["X"], mk_tyarr [tyVarX] tBool, dummy_span)
let any2any = SForall(["X"], mk_tyarr [tyVarX] tyVarX, dummy_span)
(* create more type synonyms here, if you need to *)


(* initial function environment *)
let initial_env : sourcespan scheme envt =
  List.fold_left (fun env (name, typ) -> StringMap.add name typ env) StringMap.empty [
      (*failwith "Create an initial function environment here"*)
      ("add1", int2int);
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
  failwith "Implement applying a substitution to a type environment here"
;;

let apply_subst_funenv (subst : 'a typ subst) (env : 'a scheme envt) : 'a scheme envt =
  failwith "Implement applying a substitution to a scheme environment here"
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
                    let subst1 = 
                        List.fold_left2
                        (fun subst typ typ2 -> 
                            let subst0 = unify typ typ2 loc reasons in
                                compose_subst subst subst0 )
                        [] typs typs2 
                    in
			   		let subst2 = unify typ typ2 loc reasons in
			   		compose_subst subst1 subst2
			   | _ -> failwith "unify fail: unable to unify"
	     end
    | _ -> 
    	begin match t2 with 
		 		| TyVar(id2, _) when not (occurs id2 t1) ->
		 			[(id2, t1)]
		 		| _ -> failwith "unify fail: unable to unify"
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
  failwith "Implement instantiating a type scheme here"
;;
let generalize (e : 'a typ envt) (t : 'a typ) : 'a scheme =
  failwith "Implement generalizing a type here"
;;


(* Ex 14 *)
let rec infer_exp (funenv : sourcespan scheme envt) (env : sourcespan typ envt) (e : sourcespan expr) reasons
        : (sourcespan typ subst * sourcespan typ * sourcespan expr) (* unification, result typ, rebuilt expr *)=
  let infer_app (e : 'a expr)  
        : (sourcespan typ subst * sourcespan typ * sourcespan expr) =
      let (fun_name, args, loc) =
         match e with
         | EPrim1(op, expr, loc) -> (string_of_op1 op, [expr], loc)
         | EPrim2(op, expr1, expr2, loc) -> (string_of_op2 op, [expr1; expr2], loc) 
         | EApp(fun_name, args, loc) -> (fun_name, args, loc)
         | _ -> failwith "infer_app: impossible expr"
      in
      (* lookup function scheme from funenv *)
      let scheme = find_pos funenv fun_name loc in
      (* fun_ty: type of the function *)
      let fun_ty = instantiate scheme in
      (* generate a new type variable as return type *)
      let tX = TyVar(gensym "arg", loc) in
      (* type of the arguments *)
      let (arg_substs, args_typs) = 
         List.fold_left 
         (fun (subst_so_far, args_typs) arg -> 
            let (arg_subst, arg_typ, arg) = infer_exp funenv env arg reasons in 
            (compose_subst arg_subst subst_so_far, args_typs@[arg_typ])
         ) ([], []) args
      in
      (* type of the function call *)
      let app_typ = TyArr(args_typs, tX, loc) in
      (* unification *)
      let unif_subst1 = unify fun_ty app_typ loc reasons in
      let final_subst = unif_subst1 (* ?? *) in
      let final_typ = apply_subst_typ final_subst tX in
      (final_subst, final_typ, e)   
  in

  match e with
  | ENumber(v, loc) -> ([], tInt, e)
  | EBool(v, loc) -> ([], tBool, e)
  | EId(x, loc) ->  ([], find_pos env x loc, e)
  | ELet(binds, aexpr, loc) -> 
    let (new_env, binds_subst) = 
        List.fold_left 
        (fun (env, subst) (typbind, expr, _) -> 
            let (binding_subst, binding_typ, expr) = infer_exp funenv env expr reasons in
            let (name, typ, _) = typbind in (* TODO : check given typ *)
            let subst_so_far = compose_subst subst binding_subst in
            let binding_typ = apply_subst_typ subst_so_far binding_typ in
            let new_env = StringMap.add name binding_typ env in
                (* unification ? *)
            (new_env, subst_so_far))
        (env, []) binds 
    in
    let (body_subst, body_typ, aexpr) = infer_exp funenv new_env aexpr reasons in
    let subst_so_far = compose_subst body_subst binds_subst in
    let body_typ = apply_subst_typ subst_so_far body_typ in
    (subst_so_far, body_typ, e)

  | EPrim1(op, expr, loc)         -> infer_app e
  | EPrim2(op, expr1, expr2, loc) ->  infer_app e
  | EApp(fun_name, args, loc)     -> infer_app e
  | EAnnot(expr, typ, loc) -> failwith "EAnnot: Finish implementing inferring types for expressions"
  | EIf(c, t, f, loc) ->
     let (c_subst, c_typ, c) = infer_exp funenv env c reasons in
     let (t_subst, t_typ, t) = infer_exp funenv env t reasons in
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
  | DFun(name, args, scheme, body, loc) ->
     let ((first_arg : string), _) = List.hd args in
     let tX = TyVar(gensym "arg", loc) in (* TODO: handle args correctly  *)
     let new_env = StringMap.add first_arg tX env in 
     let (b_subst, b_typ, body) = infer_exp funenv new_env body reasons in
     let final_subst = compose_subst b_subst [(first_arg, tX)] in
        (StringMap.add name (apply_subst_scheme final_subst scheme) StringMap.empty, TyArr([tX], b_typ, loc), decl)
;;

let infer_group funenv env (g : sourcespan decl list) : (sourcespan scheme envt * sourcespan decl list) =
  let fun1 = List.hd g in (* TODO *)
    let (s, t, d) = infer_decl funenv env fun1 [] in
      (s, []@[d])
;;

let infer_prog funenv env (p : sourcespan program) : sourcespan program =
  match p with
  | Program(declgroups, body, typ, tag) ->
     (*let (_, _) = infer_group funenv env (List.hd declgroups) in *)
      let (unification, result_typ, rebuilt_expr) = infer_exp funenv env body [] in 
     p (* TODO *)
;;

let type_synth (p : sourcespan program) : sourcespan program fallible =
  try
    Ok(infer_prog initial_env StringMap.empty p)
  with e -> Error([e])
;;
