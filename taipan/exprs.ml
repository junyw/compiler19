open Printf


let show_debug_print = ref false
let debug_printf fmt =
  if !show_debug_print
  then printf fmt
  else ifprintf stdout fmt
;;

type tag = int
type sourcespan = (Lexing.position * Lexing.position)

type prim1 =
  | Add1
  | Sub1
  | Print
  | PrintB
  | IsBool
  | IsNum
  | Not
  | PrintStack

type prim2 =
  | Plus
  | Minus
  | Times
  | And
  | Or
  | Greater
  | GreaterEq
  | Less
  | LessEq
  | Eq
  | EqB


type 'a typ =
  | TyBlank of 'a (* nothing was specified *)
  | TyCon of string * 'a (* type constants like Int or Bool *)
  | TyVar of string * 'a (* type variables, like 'a *)
  | TyArr of 'a typ list * 'a typ * 'a (* function types, ('a, 'b, 'c -> 'd) etc. *)
  | TyApp of 'a typ * 'a typ list * 'a (* type application, like 'a list *)

type 'a scheme =
  | SForall of string list * 'a typ * 'a (* e.g. Forall 'a, 'b, (some type using 'a, 'b) *)

type 'a typbind = (string * 'a typ * 'a)

and 'a bind = ('a typbind * 'a expr * 'a)

and 'a expr =
  | ELet of 'a bind list * 'a expr * 'a
  | EPrim1 of prim1 * 'a expr * 'a
  | EPrim2 of prim2 * 'a expr * 'a expr * 'a
  | EIf of 'a expr * 'a expr * 'a expr * 'a
  | ENumber of int * 'a
  | EBool of bool * 'a
  | EId of string * 'a
  | EApp of string * 'a expr list * 'a
  | EAnnot of 'a expr * 'a typ * 'a

type 'a decl =
  | DFun of string * (string * 'a) list * 'a scheme * 'a expr * 'a
         (* name,    args,                poly.type,  body,     tag *)

type 'a program =
  | Program of 'a decl list list * 'a expr * 'a typ * 'a (* one 'a decl list = one declgroup *)

type 'a immexpr = (* immediate expressions *)
  | ImmNum of int * 'a
  | ImmBool of bool * 'a
  | ImmId of string * 'a
and 'a cexpr = (* compound expressions *)
  | CIf of 'a immexpr * 'a aexpr * 'a aexpr * 'a
  | CPrim1 of prim1 * 'a immexpr * 'a
  | CPrim2 of prim2 * 'a immexpr * 'a immexpr * 'a
  | CApp of string * 'a immexpr list * 'a
  | CImmExpr of 'a immexpr (* for when you just need an immediate value *)
and 'a aexpr = (* anf expressions *)
  | ALet of string * 'a cexpr * 'a aexpr * 'a
  | ACExpr of 'a cexpr
and 'a adecl =
  | ADFun of string * string list * 'a aexpr * 'a

and 'a aprogram =
  | AProgram of 'a adecl list * 'a aexpr * 'a

           
let rec map_tag_E (f : 'a -> 'b) (e : 'a expr) =
  match e with
  | EId(x, a) -> EId(x, f a)
  | ENumber(n, a) -> ENumber(n, f a)
  | EBool(b, a) -> EBool(b, f a)
  | EAnnot(e, t, a) -> EAnnot(map_tag_E f e, map_tag_T f t, f a)
  | EPrim1(op, e, a) ->
     let tag_prim = f a in
     EPrim1(op, map_tag_E f e, tag_prim)
  | EPrim2(op, e1, e2, a) ->
     let tag_prim = f a in
     let tag_e1 = map_tag_E f e1 in
     let tag_e2 = map_tag_E f e2 in
     EPrim2(op, tag_e1, tag_e2, tag_prim)
  | ELet(binds, body, a) ->
     let tag_let = f a in
     let tag_bind ((x, t, ax), b, ab) =
       let tag_ax = f ax in
       let tag_ab = f ab in
       let tag_t = map_tag_T f t in
       let tag_b = map_tag_E f b in
       ((x, tag_t, tag_ax), tag_b, tag_ab) in
     let tag_binds = List.map tag_bind binds in
     let tag_body = map_tag_E f body in
     ELet(tag_binds, tag_body, tag_let)
  | EIf(cond, thn, els, a) ->
     let tag_if = f a in
     let tag_cond = map_tag_E f cond in
     let tag_thn = map_tag_E f thn in
     let tag_els = map_tag_E f els in
     EIf(tag_cond, tag_thn, tag_els, tag_if)
  | EApp(name, args, a) ->
     let tag_app = f a in
     EApp(name, List.map (map_tag_E f) args, tag_app)
and map_tag_T (f : 'a -> 'b) t =
  match t with
  | TyBlank a -> TyBlank(f a)
  | TyCon(name, a) -> TyCon(name, f a)
  | TyArr(args, ret, a) ->
     let tag_arrow = f a in
     let tag_args = List.map (map_tag_T f) args in
     let tag_ret = map_tag_T f ret in
     TyArr(tag_args, tag_ret, tag_arrow)
  | TyApp(t, args, a) ->
     let tag_app = f a in
     let tag_t = map_tag_T f t in
     let tag_args = List.map (map_tag_T f) args in
     TyApp(tag_t, tag_args, tag_app)
  | TyVar (x, a) -> TyVar(x, f a)
and map_tag_S (f : 'a -> 'b) s =
  match s with
  | SForall(vars, typ, a) -> SForall(vars, map_tag_T f typ, f a)
and map_tag_D (f : 'a -> 'b) d =
  match d with
  | DFun(name, args, scheme, body, a) ->
     let tag_fun = f a in
     let tag_args = List.map (fun (a, aa) -> (a, f aa)) args in
     let tag_scheme = map_tag_S f scheme in
     let tag_body = map_tag_E f body in
     DFun(name, tag_args, tag_scheme, tag_body, tag_fun)
and map_tag_P (f : 'a -> 'b) p =
  match p with
  | Program(declgroups, body, typ, a) ->
     let tag_a = f a in
     let tag_decls = List.map (fun group -> List.map (map_tag_D f) group) declgroups in
     let tag_body = map_tag_E f body in
     let tag_typ = map_tag_T f typ in
     Program(tag_decls, tag_body, tag_typ, tag_a)

let tag (p : 'a program) : tag program =
  let next = ref 0 in
  let tag _ =
    next := !next + 1;
    !next in
  map_tag_P tag p
;;

           
let combine_tags (f1 : 'a -> 'b) (f2 : 'a -> 'c) (p : 'a program) : ('b * 'c) program =
  map_tag_P (fun a -> (f1 a, f2 a)) p
;;
let tag_and_map (f : 'a -> 'b) (p : 'a program) : ('a * 'b) program =
  map_tag_P (fun a -> (a, f a)) p
;;
let prog_and_tag (p : 'a program) : ('a * tag) program =
  let next = ref 0 in
  let tag _ =
    next := !next + 1;
    !next in
  tag_and_map tag p
;;
           
let untag (p : 'a program) : unit program =
  let rec helpE e =
    match e with
    | EId(x, _) -> EId(x, ())
    | ENumber(n, _) -> ENumber(n, ())
    | EBool(b, _) -> EBool(b, ())
    | EAnnot(e, t, _) -> EAnnot(helpE e, helpT t, ())
    | EPrim1(op, e, _) ->
       EPrim1(op, helpE e, ())
    | EPrim2(op, e1, e2, _) ->
       EPrim2(op, helpE e1, helpE e2, ())
    | ELet(binds, body, _) ->
       ELet(List.map(fun (x, b, _) -> (x, helpE b, ())) binds, helpE body, ())
    | EIf(cond, thn, els, _) ->
       EIf(helpE cond, helpE thn, helpE els, ())
    | EApp(name, args, _) ->
       EApp(name, List.map helpE args, ())
  and helpT t =
    match t with
    | TyBlank _ -> TyBlank ()
    | TyCon(name, _) -> TyCon(name, ())
    | TyArr(args, ret, _) -> TyArr(List.map helpT args, helpT ret, ())
    | TyApp(t, args, _) -> TyApp(helpT t, List.map helpT args, ())
    | TyVar(x, _) -> TyVar(x, ())
  and helpS s =
    match s with
    | SForall(vars, typ, _) -> SForall(vars, helpT typ, ())
  and helpD d =
    match d with
    | DFun(name, args, scheme, body, _) ->
       DFun(name, List.map (fun (a, _) -> (a, ())) args, helpS scheme, helpE body, ())
  and helpP p =
    match p with
    | Program(decls, body, typ, _) ->
       Program(List.map (fun group -> List.map helpD group) decls, helpE body, helpT typ, ())
  in helpP p

let atag (p : 'a aprogram) : tag aprogram =
  let next = ref 0 in
  let tag () =
    next := !next + 1;
    !next in
  let rec helpA (e : 'a aexpr) : tag aexpr =
    match e with
    | ALet(x, c, b, _) ->
       let let_tag = tag() in
       ALet(x, helpC c, helpA b, let_tag)
    | ACExpr c -> ACExpr (helpC c)
  and helpC (c : 'a cexpr) : tag cexpr =
    match c with
    | CPrim1(op, e, _) ->
       let prim_tag = tag() in
       CPrim1(op, helpI e, prim_tag)
    | CPrim2(op, e1, e2, _) ->
       let prim_tag = tag() in
       CPrim2(op, helpI e1, helpI e2, prim_tag)
    | CIf(cond, thn, els, _) ->
       let if_tag = tag() in
       CIf(helpI cond, helpA thn, helpA els, if_tag)
    | CApp(name, args, _) ->
       let app_tag = tag() in
       CApp(name, List.map helpI args, app_tag)
    | CImmExpr i -> CImmExpr (helpI i)
  and helpI (i : 'a immexpr) : tag immexpr =
    match i with
    | ImmId(x, _) -> ImmId(x, tag())
    | ImmNum(n, _) -> ImmNum(n, tag())
    | ImmBool(b, _) -> ImmBool(b, tag())
  and helpD d =
    match d with
    | ADFun(name, args, body, _) ->
       let fun_tag = tag() in
       ADFun(name, args, helpA body, fun_tag)
  and helpP p =
    match p with
    | AProgram(decls, body, _) ->
       AProgram(List.map helpD decls, helpA body, 0)
  in helpP p
