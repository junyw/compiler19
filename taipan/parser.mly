%{
open Exprs

%}

%token <int> NUM
%token <string> ID TYID
%token DEF ANDDEF ADD1 SUB1 LPARENSPACE LPARENNOSPACE RPAREN LET IN EQUAL COMMA PLUS MINUS TIMES IF COLON ELSECOLON EOF PRINT PRINTSTACK TRUE FALSE ISBOOL ISNUM EQEQ LESSSPACE LESSNOSPACE GREATER LESSEQ GREATEREQ AND OR NOT THINARROW

%left PLUS MINUS TIMES GREATER LESSSPACE LESSNOSPACE GREATEREQ LESSEQ EQEQ AND OR


%type <(Lexing.position * Lexing.position) Exprs.program> program

%start program

%%

const :
  | NUM { ENumber($1, (Parsing.symbol_start_pos (), Parsing.symbol_end_pos ())) }
  | TRUE { EBool(true, (Parsing.symbol_start_pos (), Parsing.symbol_end_pos ())) }
  | FALSE { EBool(false, (Parsing.symbol_start_pos (), Parsing.symbol_end_pos ())) }

prim1 :
  | ADD1 { Add1 }
  | SUB1 { Sub1 }
  | NOT { Not }
  | PRINT { Print }
  | ISBOOL { IsBool }
  | ISNUM { IsNum }
  | PRINTSTACK { PrintStack }

binds :
  | bind EQUAL expr { [($1, $3, (Parsing.rhs_start_pos 1, Parsing.rhs_end_pos 1))] }
  | bind EQUAL expr COMMA binds { ($1, $3, (Parsing.rhs_start_pos 1, Parsing.rhs_end_pos 1))::$5 }

binop_expr :
  | prim1 LPARENNOSPACE expr RPAREN { EPrim1($1, $3, (Parsing.symbol_start_pos (), Parsing.symbol_end_pos ())) }
  | ID LPARENNOSPACE exprs RPAREN { EApp($1, $3, (Parsing.symbol_start_pos (), Parsing.symbol_end_pos ())) }
  | ID LPARENNOSPACE RPAREN { EApp($1, [], (Parsing.symbol_start_pos (), Parsing.symbol_end_pos ())) }
  | LPARENSPACE expr RPAREN { $2 }
  | LPARENNOSPACE expr RPAREN { $2 }
  | binop_expr PLUS binop_expr { EPrim2(Plus, $1, $3, (Parsing.symbol_start_pos (), Parsing.symbol_end_pos ())) }
  | binop_expr MINUS binop_expr { EPrim2(Minus, $1, $3, (Parsing.symbol_start_pos (), Parsing.symbol_end_pos ())) }
  | binop_expr TIMES binop_expr { EPrim2(Times, $1, $3, (Parsing.symbol_start_pos (), Parsing.symbol_end_pos ())) }
  | binop_expr AND binop_expr { EPrim2(And, $1, $3, (Parsing.symbol_start_pos (), Parsing.symbol_end_pos ())) }
  | binop_expr OR binop_expr { EPrim2(Or, $1, $3, (Parsing.symbol_start_pos (), Parsing.symbol_end_pos ())) }
  | binop_expr GREATER binop_expr { EPrim2(Greater, $1, $3, (Parsing.symbol_start_pos (), Parsing.symbol_end_pos ())) }
  | binop_expr GREATEREQ binop_expr { EPrim2(GreaterEq, $1, $3, (Parsing.symbol_start_pos (), Parsing.symbol_end_pos ())) }
  | binop_expr LESSSPACE binop_expr { EPrim2(Less, $1, $3, (Parsing.symbol_start_pos (), Parsing.symbol_end_pos ())) }
  | binop_expr LESSNOSPACE binop_expr { EPrim2(Less, $1, $3, (Parsing.symbol_start_pos (), Parsing.symbol_end_pos ())) }
  | binop_expr LESSEQ binop_expr { EPrim2(LessEq, $1, $3, (Parsing.symbol_start_pos (), Parsing.symbol_end_pos ())) }
  | binop_expr EQEQ binop_expr { EPrim2(Eq, $1, $3, (Parsing.symbol_start_pos (), Parsing.symbol_end_pos ())) }
  | const { $1 }
  | ID { EId($1, (Parsing.symbol_start_pos (), Parsing.symbol_end_pos ())) }

expr :
  | LET binds IN expr { ELet($2, $4, (Parsing.symbol_start_pos (), Parsing.symbol_end_pos ())) }
  | IF expr COLON expr ELSECOLON expr { EIf($2, $4, $6, (Parsing.symbol_start_pos (), Parsing.symbol_end_pos ())) }
  | binop_expr { $1 }

exprs :
  | expr { [$1] }
  | expr COMMA exprs { $1::$3 }

decl :
  | DEF ID LPARENNOSPACE RPAREN COLON expr
    { let arg_pos = Parsing.rhs_start_pos 3, Parsing.rhs_end_pos 4 in
      DFun($2, [], SForall([], TyArr([], TyBlank arg_pos, arg_pos), arg_pos), $6, (Parsing.symbol_start_pos (), Parsing.symbol_end_pos ())) }
  | DEF ID LPARENNOSPACE RPAREN THINARROW typ COLON expr
    {
      let typ_pos = (Parsing.rhs_start_pos 6, Parsing.rhs_end_pos 6) in
      DFun($2, [], SForall([], TyArr([], $6, typ_pos), typ_pos), $8, (Parsing.symbol_start_pos (), Parsing.symbol_end_pos ())) }
  | DEF ID LESSNOSPACE tyids GREATER LPARENNOSPACE ids RPAREN THINARROW typ COLON expr
    {
      let arg_names = List.map (fun (name, _, a) -> (name, a)) $7 in
      let arg_types = List.map (fun (_, typ, _) -> typ) $7 in
      let arrow_pos = (Parsing.rhs_start_pos 6, Parsing.rhs_end_pos 10) in
      let typ_pos = (Parsing.rhs_start_pos 3, Parsing.rhs_end_pos 10) in
      DFun($2, arg_names, SForall($4, TyArr(arg_types, $10, arrow_pos), typ_pos), $12, (Parsing.symbol_start_pos (), Parsing.symbol_end_pos ()))
    }
  | DEF ID LPARENNOSPACE ids RPAREN COLON expr
    {
      let arg_names = List.map (fun (name, _, a) -> (name, a)) $4 in
      let arg_types = List.map (fun (_, typ, _) -> typ) $4 in
      let typ_pos = (Parsing.rhs_start_pos 3, Parsing.rhs_end_pos 5) in
      let arr_typ = SForall([], TyArr(arg_types, TyBlank(typ_pos), typ_pos), typ_pos) in
      DFun($2, arg_names, arr_typ, $7, (Parsing.symbol_start_pos (), Parsing.symbol_end_pos ()))
    }
  | DEF ID LPARENNOSPACE ids RPAREN THINARROW typ COLON expr
    {
      let arg_names = List.map (fun (name, _, a) -> (name, a)) $4 in
      let arg_types = List.map (fun (_, typ, _) -> typ) $4 in
      let typ_pos = (Parsing.rhs_start_pos 3, Parsing.rhs_end_pos 7) in
      DFun($2, arg_names, SForall([], TyArr(arg_types, $7, typ_pos), typ_pos), $9, (Parsing.symbol_start_pos (), Parsing.symbol_end_pos ()))
    }

tyids :
  | { [] }
  | TYID COMMA tyids { $1::$3 }

tyid : TYID { TyVar($1, (Parsing.symbol_start_pos (), Parsing.symbol_end_pos ())) }

ids :
  | bind { [$1] }
  | bind COMMA ids { $1::$3 }

bind :
  | ID { ($1, TyBlank(Parsing.symbol_start_pos (), Parsing.symbol_end_pos ()), (Parsing.symbol_start_pos (), Parsing.symbol_end_pos ())) }
  | ID COLON typ { ($1, $3, (Parsing.symbol_start_pos (), Parsing.symbol_end_pos ())) }

typ :
  | ID { TyCon($1, (Parsing.symbol_start_pos (), Parsing.symbol_end_pos ())) }
  | tyid { $1 }
  | LPARENNOSPACE typs THINARROW typ RPAREN { TyArr($2, $4, (Parsing.symbol_start_pos (), Parsing.symbol_end_pos ())) }
  | LPARENSPACE typs THINARROW typ RPAREN { TyArr($2, $4, (Parsing.symbol_start_pos (), Parsing.symbol_end_pos ())) }
typs :
  | typ { [$1] }
  | typ COMMA typs { $1::$3 }

declgroup :
  | decl { [$1] }
  | decl ANDDEF declgroup { $1::$3 }

decls :
  | declgroup { [$1] }
  | declgroup decls { $1::$2 }

program :
  | decls expr COLON typ EOF { Program($1, $2, $4, (Parsing.symbol_start_pos (), Parsing.symbol_end_pos ())) }
  | decls expr EOF { Program($1, $2, TyBlank(Parsing.symbol_end_pos(), Parsing.symbol_end_pos()), (Parsing.symbol_start_pos (), Parsing.symbol_end_pos ())) }
  | expr COLON typ EOF { Program([], $1, $3, (Parsing.symbol_start_pos (), Parsing.symbol_end_pos ())) }
  | expr EOF { Program([], $1, TyBlank(Parsing.symbol_end_pos(), Parsing.symbol_end_pos()), (Parsing.symbol_start_pos (), Parsing.symbol_end_pos ())) }

%%
