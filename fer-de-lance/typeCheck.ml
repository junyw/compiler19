open Exprs
open Errors
open Printf
open Pretty
open Phases

type 'a envt = (string * 'a) list;;

let dummy_span = (Lexing.dummy_pos, Lexing.dummy_pos)
             
let tInt = TyCon("Int", dummy_span)
let tBool = TyCon("Bool", dummy_span)
let intint2int = SForall([], TyArr([tInt; tInt], tInt, dummy_span), dummy_span)
let int2bool = SForall([], TyArr([tInt], tBool, dummy_span), dummy_span)
let tyVarX = TyVar("X", dummy_span)
let any2bool = SForall(["X"], TyArr([tyVarX], tBool, dummy_span), dummy_span)
let any2any = SForall(["X"], TyArr([tyVarX], tyVarX, dummy_span), dummy_span)
(* create more type synonyms here, if you need to *)
let initial_env : sourcespan typ envt =
  [
    failwith "Create an initial function environment here"
  ]

let rec find_pos ls x pos =
  match ls with
  | [] -> failwith (sprintf "Name %s not found at %s" x (string_of_sourcespan pos))
  | (y,v)::rest ->
     if y = x then v else find_pos rest x pos

let type_check (p : sourcespan program) : sourcespan program fallible =
  let rec same_typ t1 t2 =
    failwith "Implement sameness checking for types"
  in
  let rec checkP ((errs : exn list), (env : sourcespan typ envt)) (p : sourcespan program) =
    failwith "Implement type checking for programs"
  and checkG ((errs : exn list), (env : sourcespan typ envt)) (d : sourcespan decl list) =
    failwith "Implement type checking for declaration groups"
  and checkD ((errs : exn list), (env : sourcespan typ envt)) (d : sourcespan decl) =
    failwith "Implement type checking for declarations"
  and checkE ((errs : exn list), (env : sourcespan typ envt)) (e : sourcespan expr) (t : sourcespan typ) =
    failwith "Implement type checking for expressions"
  in match checkP ([], initial_env) p with
     | ([], _) -> Ok p
     | (exns, _) -> Error (List.rev exns)
;;
