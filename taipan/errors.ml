open Printf
open Exprs
open Pretty

(* TODO: Define any additional exceptions you want *)
exception ParseError of string (* parse-error message *)
exception UnboundId of string * sourcespan (* name, where used *)
exception UnboundFun of string * sourcespan (* name of fun, where used *)
exception ShadowId of string * sourcespan * sourcespan (* name, where used, where defined *)
exception DuplicateId of string * sourcespan * sourcespan (* name, where used, where defined *)
exception DuplicateFun of string * sourcespan * sourcespan (* name, where used, where defined *)
exception Overflow of int * sourcespan (* value, where used *)
exception Arity of int * int * sourcespan (* intended arity, actual arity, where called *)
exception NotYetImplemented of string (* TODO: Message to show *)
exception InternalCompilerError of string (* Major failure: message to show *)


type reason =
  | InferExp of sourcespan expr
  | Message of string
  | Unify of string * sourcespan typ * sourcespan typ
  | Instantiate of string * sourcespan scheme
                                     
exception NoType of string * sourcespan (* name, where defined *)
exception ShouldBeFunction of string * sourcespan * sourcespan typ (* name, where defined, actual typ *)
exception TypeMismatch of sourcespan * sourcespan typ * sourcespan typ * reason list (* where, expected, actual *)
exception DeclArity of string * int * int * sourcespan (* name, num args, num types, where defined *)


  

(* Stringifies a list of compilation errors *)
let print_errors (exns : exn list) : string list =
  List.map (fun e ->
      match e with
      | ParseError msg -> msg
      | NotYetImplemented msg ->
         "Not yet implemented: " ^ msg
      | InternalCompilerError msg ->
         "Internal Compiler Error: " ^ msg
      | UnboundId(x, loc) ->
         sprintf "The identifier %s, used at <%s>, is not in scope" x (string_of_sourcespan loc)
      | UnboundFun(x, loc) ->
         sprintf "The function name %s, used at <%s>, is not in scope" x (string_of_sourcespan loc)
      | ShadowId(x, loc, existing) ->
         sprintf "The identifier %s, defined at <%s>, shadows one defined at <%s>"
                 x (string_of_sourcespan loc) (string_of_sourcespan existing)
      | DuplicateId(x, loc, existing) ->
         sprintf "The identifier %s, redefined at <%s>, duplicates one at <%s>"
                 x (string_of_sourcespan loc) (string_of_sourcespan existing)
      | DuplicateFun(x, loc, existing) ->
         sprintf "The function name %s, redefined at <%s>, duplicates one at <%s>"
                 x (string_of_sourcespan loc) (string_of_sourcespan existing)
      | Overflow(num, loc) ->
         sprintf "The number literal %d, used at <%s>, is not supported in this language"
                 num (string_of_sourcespan loc)
      | Arity(expected, actual, loc) ->
         sprintf "The function called at <%s> expected an arity of %d, but received %d arguments"
                 (string_of_sourcespan loc) expected actual
      | NoType(name, loc) ->
         sprintf "The function %s at <%s> has no type defined" name (string_of_sourcespan loc)
      | DeclArity(name, num_args, num_types, loc) ->
         sprintf "The function %s, defined at %s, has %d arguments but only %d types provided"
                 name (string_of_sourcespan loc) num_args num_types
      | ShouldBeFunction(name, loc, wanted) ->
         sprintf "The function %s, at %s, should have function type %s" name (string_of_sourcespan loc) (string_of_typ wanted)
      | TypeMismatch(loc, expected, actual, []) ->
          sprintf "Type error at %s: expected %s but got %s"
            (string_of_sourcespan loc) (string_of_typ expected) (string_of_typ actual)
      | TypeMismatch(loc, expected, actual, reasons) ->
         let get_tag e = match e with
           | ELet(_, _, t) -> t
           | EPrim1(_, _, t) -> t
           | EPrim2(_, _, _, t) -> t
           | EIf(_, _, _, t) -> t
           | ENumber(_, t) -> t
           | EBool(_, t) -> t
           | EId(_, t) -> t
           | EApp(_, _, t) -> t
           | EAnnot(_, _, t) -> t in
         let print_reason r =
           match r with
           | InferExp e -> sprintf "\ttrying to infer type for %s at %s"
                             (string_of_expr e) (string_of_sourcespan (get_tag e))
           | Message s -> "\t" ^ s
           | Unify(s, t1, t2) -> sprintf "\ttrying to unify %s and %s (because %s)"
                                   (string_of_typ t1) (string_of_typ t2) s
           | Instantiate(name, scheme) -> sprintf "\ttrying to instantiate %s at %s" name (string_of_scheme scheme) in
          sprintf "Type error at %s: expected %s but got %s, because\n%s"
            (string_of_sourcespan loc) (string_of_typ expected) (string_of_typ actual)
            (ExtString.String.join "\n" (List.map print_reason reasons))
      | _ ->
         sprintf "%s" (Printexc.to_string e)
    ) exns
;;

