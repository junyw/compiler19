open Exprs
open Printf
open Format
open Lexing

let rec intersperse (elts : 'a list) (sep : 'a) : 'a list =
  match elts with
  | [] -> []
  | [elt] -> [elt]
  | elt::rest -> elt::sep::(intersperse rest sep)

let string_of_op1 op =
  match op with
  | Add1 -> "add1"
  | Sub1 -> "sub1"
  | Print -> "print"
  | PrintB -> "print?"
  | PrintStack -> "printStack"
  | Not -> "!"
  | IsNum -> "isnum"
  | IsBool -> "isbool"

let name_of_op1 op =
  match op with
  | Add1 -> "Add1"
  | Sub1 -> "Sub1"
  | Print -> "Print"
  | PrintB -> "PrintB"
  | PrintStack -> "PrintStack"
  | Not -> "Not"
  | IsNum -> "IsNum"
  | IsBool -> "IsBool"

let string_of_op2 op =
  match op with
  | Plus -> "+"
  | Minus -> "-"
  | Times -> "*"
  | And -> "&&"
  | Or -> "||"
  | Greater -> ">"
  | Less -> "<"
  | GreaterEq -> ">="
  | LessEq -> "<="
  | Eq -> "=="
  | EqB -> "=?"
let name_of_op2 op =
  match op with
  | Plus -> "Plus"
  | Minus -> "Minus"
  | Times -> "Times"
  | And -> "And"
  | Or -> "Or"
  | Greater -> "Greater"
  | Less -> "Less"
  | GreaterEq -> "GreaterEq"
  | LessEq -> "LessEq"
  | Eq -> "Eq"
  | EqB -> "EqB"
               

let rec string_of_typ (t : 'a typ) : string =
  match t with
  | TyBlank _ -> "<BLANK>"
  | TyCon(name, _) -> name
  | TyArr(args, ret, _) -> sprintf "(%s -> %s)"
                              (ExtString.String.join ", " (List.map string_of_typ args))
                              (string_of_typ ret)
  | TyApp(t, args, _) -> sprintf "%s<%s>"
                           (string_of_typ t)
                           (ExtString.String.join ", " (List.map string_of_typ args))
  | TyVar (id, _) -> "'" ^ id
let string_of_scheme (s : 'a scheme) : string =
  match s with
  | SForall(vars, typ, _) -> sprintf "Forall %s, %s" (ExtString.String.join ", " vars) (string_of_typ typ)

let string_of_typbind ((name, typ, _) : 'a typbind) : string =
  match typ with
  | TyBlank _ -> name
  | _ -> sprintf "%s : %s" name (string_of_typ typ)

let rec string_of_bind_with (print_a : 'a -> string) ((bind, expr, _) : 'a bind) : string =
  sprintf "%s = %s" (string_of_typbind bind) (string_of_expr_with print_a expr)
and string_of_bind (b : 'a bind) : string =
  string_of_bind_with (fun _ -> "") b

and string_of_expr_with (print_a : 'a -> string) (e : 'a expr) : string =
  let string_of_expr = string_of_expr_with print_a in
  match e with
  | ENumber(n, a) -> (string_of_int n) ^ (print_a a)
  | EBool(b, a) -> (string_of_bool b) ^ (print_a a)
  | EId(x, a) -> x ^ (print_a a)
  | EAnnot(e, t, a) -> "(" ^ (string_of_expr e) ^ ")::" ^ (string_of_typ t) ^ (print_a a)
  | EPrim1(op, e, a) ->
     sprintf "%s(%s)%s" (string_of_op1 op) (string_of_expr e) (print_a a)
  | EPrim2(op, left, right, a) ->
     sprintf "(%s %s %s)%s" (string_of_expr left) (string_of_op2 op) (string_of_expr right) (print_a a)
  | ELet(binds, body, a) ->
     let binds_strs = List.map (fun ((x, t, _), e, _) -> sprintf "%s : %s = %s" x (string_of_typ t) (string_of_expr e)) binds in
     let binds_str = List.fold_left (^) "" (intersperse binds_strs ", ") in
     sprintf "(let %s in %s)%s" binds_str (string_of_expr body) (print_a a)
  | EIf(cond, thn, els, a) ->
     sprintf "(if %s: %s else: %s)%s"
             (string_of_expr cond)
             (string_of_expr thn)
             (string_of_expr els)
             (print_a a)
  | EApp(funname, args, a) ->
     sprintf "(%s(%s))%s" funname (ExtString.String.join ", " (List.map string_of_expr args)) (print_a a)
let string_of_expr (e : 'a expr) : string =
  string_of_expr_with (fun _ -> "") e

let string_of_decl_with (print_a : 'a -> string) (d : 'a decl) : string =
  match d with
  | DFun(name, args, _, body, a) ->
     sprintf "(def %s(%s):\n  %s)%s"
       name
       (ExtString.String.join ", " (List.map (fun (arg, a) -> sprintf "%s%s" arg (print_a a)) args))
       (string_of_expr_with print_a body) (print_a a)
let string_of_decl (d : 'a decl) : string =
  string_of_decl_with (fun _ -> "") d

let string_of_program_with (print_a : 'a -> string) (p : 'a program) : string =
  match p with
  | Program(decls, body, typ, a) ->
     let typ_str = match typ with
       | TyBlank _ -> ""
       | _ -> " : " ^ string_of_typ typ in
     let help group =
       ExtString.String.join "\nand " (List.map (string_of_decl_with print_a) group) in
     (ExtString.String.join "\n\n" (List.map help decls)) ^ "\n" ^
       (string_of_expr_with print_a body) ^ typ_str ^ "\n" ^ (print_a a)
let string_of_program (p : 'a program) : string =
  string_of_program_with (fun _ -> "") p


let string_of_position (p : position) : string =
  sprintf "%s:line %d, col %d" p.pos_fname p.pos_lnum (p.pos_cnum - p.pos_bol);;

let string_of_sourcespan ((pstart, pend) : sourcespan) : string =
  sprintf "%s, %d:%d-%d:%d" pstart.pos_fname pstart.pos_lnum (pstart.pos_cnum - pstart.pos_bol)
          pend.pos_lnum (pend.pos_cnum - pend.pos_bol)

let rec string_of_aexpr_with (print_a : 'a -> string) (e : 'a aexpr) : string =
  let string_of_aexpr = string_of_aexpr_with print_a in
  match e with
  | ALet(x, e, b, a) -> sprintf "(alet %s = %s in %s)%s" x (string_of_cexpr_with print_a e) (string_of_aexpr b) (print_a a)
  | ACExpr c -> string_of_cexpr_with print_a c
and string_of_cexpr_with (print_a : 'a -> string) (c : 'a cexpr) : string =
  let string_of_aexpr = string_of_aexpr_with print_a in
  let string_of_immexpr = string_of_immexpr_with print_a in
  match c with
  | CPrim1(op, e, a) ->
     sprintf "%s(%s)%s" (string_of_op1 op) (string_of_immexpr e) (print_a a)
  | CPrim2(op, left, right, a) ->
     sprintf "(%s %s %s)%s" (string_of_immexpr left) (string_of_op2 op) (string_of_immexpr right) (print_a a)
  | CIf(cond, thn, els, a) ->
     sprintf "(if %s: %s else: %s)%s"
             (string_of_immexpr cond)
             (string_of_aexpr thn)
             (string_of_aexpr els)
             (print_a a)
  | CApp(funname, args, a) ->
     sprintf "(%s(%s))%s" funname (ExtString.String.join ", " (List.map string_of_immexpr args)) (print_a a)
  | CImmExpr i -> string_of_immexpr i
and string_of_immexpr_with (print_a : 'a -> string) (i : 'a immexpr) : string =
  match i with
  | ImmNum(n, a) -> (string_of_int n) ^ (print_a a)
  | ImmBool(b, a) -> (string_of_bool b) ^ (print_a a)
  | ImmId(x, a) -> x ^ (print_a a)
and string_of_aprogram_with (print_a : 'a -> string) (p : 'a aprogram) : string =
  match p with
  | AProgram(decls, body, a) ->
     (ExtString.String.join "\n" (List.map (string_of_adecl_with print_a) decls)) ^ "\n"
     ^ (string_of_aexpr_with print_a body) ^ "\n" ^ (print_a a)
and string_of_adecl_with (print_a : 'a -> string) (d : 'a adecl) : string =
  match d with
  | ADFun(name, args, body, a) ->
     sprintf "(fun %s(%s): %s)%s" name (ExtString.String.join ", " args)
       (string_of_aexpr_with print_a body) (print_a a)

let string_of_aexpr (e : 'a aexpr) : string = string_of_aexpr_with (fun _ -> "") e
let string_of_cexpr (c : 'a cexpr) : string = string_of_cexpr_with (fun _ -> "") c
let string_of_immexpr (i : 'a immexpr) : string = string_of_immexpr_with (fun _ -> "") i
let string_of_adecl (d : 'a adecl) : string = string_of_adecl_with (fun _ -> "") d
let string_of_aprogram (p : 'a aprogram) : string = string_of_aprogram_with (fun _ -> "") p
;;
let print_list fmt p_item items p_sep =
  match items with
  | [] -> ()
  | [item] -> p_item fmt item
  | first::rest ->
     p_item fmt first;
     List.iter (fun item -> p_sep fmt; p_item fmt item) rest;;
let indent = 2
let print_comma_sep fmt =
  pp_print_string fmt ","; pp_print_space fmt ();;
let maybe_angle str = 
  if str = "" then "" else "<" ^ str ^ ">";;
let open_label fmt label a =
  pp_open_hvbox fmt indent; pp_print_string fmt label; pp_print_string fmt (maybe_angle a);
  pp_print_string fmt "("; pp_print_cut fmt ();;
let open_paren fmt =
  pp_open_box fmt indent; pp_print_string fmt "("; pp_print_cut fmt ();;
let open_angle fmt =
  pp_open_box fmt indent; pp_print_string fmt "<"; pp_print_cut fmt ();;
let close_paren fmt =
  pp_print_break fmt 0 (~-indent); pp_close_box fmt (); pp_print_string fmt ")";;
let close_angle fmt =
  pp_print_break fmt 0 (~-indent); pp_close_box fmt (); pp_print_string fmt ">";;
let quote x = "\"" ^ x ^ "\"";;


let rec format_typ (fmt : Format.formatter) (print_a : 'a -> string) (t : 'a typ) : unit =
  let help fmt = format_typ fmt print_a in
  match t with
  | TyBlank a -> pp_print_string fmt "<BLANK>"; pp_print_string fmt (maybe_angle (print_a a))
  | TyCon(name, a) -> pp_print_string fmt name; pp_print_string fmt (maybe_angle (print_a a))
  | TyVar(name, a) -> pp_print_string fmt "'"; pp_print_string fmt name; pp_print_string fmt (maybe_angle (print_a a))
  | TyArr(args, ret, a) ->
     open_paren fmt; print_list fmt help args print_comma_sep;
     pp_print_string fmt " ->"; pp_print_string fmt (maybe_angle (print_a a)); pp_print_string fmt " ";
     help fmt ret;
     close_paren fmt
  | TyApp(typ, args, a) ->
     help fmt typ;
     open_angle fmt;
     print_list fmt help args print_comma_sep;
     close_angle fmt; pp_print_string fmt (maybe_angle (print_a a)); pp_print_string fmt " ";
;;
let rec format_expr (fmt : Format.formatter) (print_a : 'a -> string) (e : 'a expr) : unit =
  let help = format_expr fmt print_a in
  match e with
  | ENumber(n, a) ->
     open_label fmt "ENumber" (print_a a);
     pp_print_int fmt n;
     close_paren fmt
  | EBool(b, a) ->
     open_label fmt "EBool" (print_a a);
     pp_print_bool fmt b;
     close_paren fmt
  | EId(x, a) ->
     open_label fmt "EId" (print_a a);
     pp_print_string fmt (quote x);
     close_paren fmt
  | EAnnot(e, t, a) ->
     pp_print_string fmt "(";
     help e;
     pp_print_string fmt "::";
     format_typ fmt print_a t;
     pp_print_string fmt ")"
  | EPrim1(op, e, a) ->
     open_label fmt "EPrim1" (print_a a);
     pp_print_string fmt (name_of_op1 op);
     print_comma_sep fmt; help e; 
     close_paren fmt
  | EPrim2(op, e1, e2, a) ->
     open_label fmt "EPrim2" (print_a a);
     pp_print_string fmt (name_of_op2 op);
     print_comma_sep fmt; help e1; print_comma_sep fmt; help e2;
     close_paren fmt
  | EIf(cond, thn, els, a) ->
     open_label fmt "EIf" (print_a a);
     help cond; print_comma_sep fmt; help thn; print_comma_sep fmt; help els;
     close_paren fmt
  | EApp(funname, args, a) ->
     open_label fmt "EApp" (print_a a);
     pp_print_string fmt (quote funname);
     print_comma_sep fmt;
     print_list fmt (fun fmt -> format_expr fmt print_a) args print_comma_sep;
     close_paren fmt
  | ELet(binds, body, a) ->
     let print_item fmt (x, b, a) =
       open_paren fmt;
       let maybe_a = maybe_angle (print_a a) in
       pp_print_string fmt (" " ^ (string_of_typbind x)); pp_print_string fmt maybe_a; print_comma_sep fmt; help b;
       close_paren fmt in
     open_label fmt "ELet" (print_a a);
     open_paren fmt; print_list fmt print_item binds print_comma_sep; close_paren fmt;
     print_comma_sep fmt;
     help body;
     close_paren fmt
;;
let format_scheme (fmt : Format.formatter) (print_a : 'a -> string) (s : 'a scheme) : unit =
  match s with
  | SForall(args, typ, a) ->
     open_label fmt "Forall" (print_a a);
     print_list fmt pp_print_string args print_comma_sep;
     pp_print_string fmt ", ";
     format_typ fmt print_a typ;
     close_paren fmt                
;;
let format_decl (fmt : Format.formatter) (print_a : 'a -> string) (d : 'a decl) : unit =
  match d with
  | DFun(name, args, scheme, body, a) ->
     open_label fmt "DFun" (print_a a);
     pp_print_string fmt ("Name: " ^ name);
     print_comma_sep fmt;
     pp_print_string fmt "Args: "; open_paren fmt;
     print_list fmt (fun fmt (arg, a) -> pp_print_string fmt arg; pp_print_string fmt (maybe_angle (print_a a))) args print_comma_sep;
     close_paren fmt;
     print_comma_sep fmt;
     pp_print_string fmt "Scheme: ";
     format_scheme fmt print_a scheme;
     print_comma_sep fmt;
     pp_print_string fmt "Body: "; open_paren fmt;
     format_expr fmt print_a body;
     close_paren fmt; close_paren fmt
;;
let format_declgroup (fmt : Format.formatter) (print_a : 'a -> string) (d : 'a decl list) : unit =
  print_list fmt (fun fmt -> format_decl fmt print_a) d (fun fmt -> pp_print_break fmt 1 0; pp_print_string fmt "and ")
;;
let format_program (fmt : Format.formatter) (print_a : 'a -> string) (p : 'a program) : unit =
  match p with
  | Program(decls, body, typ, a) ->
     print_list fmt (fun fmt -> format_declgroup fmt print_a) decls (fun fmt -> pp_print_break fmt 1 0);
     pp_print_break fmt 1 0;
     format_expr fmt print_a body
;;


let ast_of_pos_expr (e : sourcespan expr) : string =
  format_expr str_formatter string_of_sourcespan e;
  flush_str_formatter ()
;;
let ast_of_expr (e : 'a expr) : string =
  format_expr str_formatter (fun _ -> "") e;
  flush_str_formatter ()
;;

let ast_of_pos_decl (d : sourcespan decl) : string =
  format_decl str_formatter string_of_sourcespan d;
  flush_str_formatter ()
;;
let ast_of_decl (d : 'a decl) : string =
  format_decl str_formatter (fun _ -> "") d;
  flush_str_formatter ()
;;

let ast_of_pos_program (p : sourcespan program) : string =
  format_program str_formatter string_of_sourcespan p;
  flush_str_formatter ()
;;
let ast_of_program (p : 'a program) : string =
  format_program str_formatter (fun _ -> "") p;
  flush_str_formatter ()
;;
