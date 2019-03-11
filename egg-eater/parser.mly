%{
open Exprs

%}

%token <int> NUM
%token <string> ID TYID
%token DEF ANDDEF ADD1 SUB1 LPARENSPACE LPARENNOSPACE RPAREN LBRACK RBRACK LBRACE RBRACE LET IN OF EQUAL COMMA PLUS MINUS TIMES IF COLON ELSECOLON EOF PRINT PRINTSTACK TRUE FALSE ISBOOL ISNUM ISTUPLE EQEQ LESSSPACE LESSNOSPACE GREATER LESSEQ GREATEREQ AND OR NOT THINARROW COLONEQ SEMI NIL TYPE

%right SEMI
%left COLON
%left PLUS MINUS TIMES GREATER LESSSPACE LESSNOSPACE GREATEREQ LESSEQ EQEQ AND OR
%left LPARENNOSPACE


%type <(Lexing.position * Lexing.position) Exprs.program> program

%start program

%%

const :
  | NUM { ENumber($1, (Parsing.symbol_start_pos (), Parsing.symbol_end_pos ())) }
  | TRUE { EBool(true, (Parsing.symbol_start_pos (), Parsing.symbol_end_pos ())) }
  | FALSE { EBool(false, (Parsing.symbol_start_pos (), Parsing.symbol_end_pos ())) }
  | NIL COLON typ { ENil($3, (Parsing.symbol_start_pos (), Parsing.symbol_end_pos ())) }

prim1 :
  | ADD1 { Add1 }
  | SUB1 { Sub1 }
  | NOT { Not }
  | PRINT { Print }
  | ISBOOL { IsBool }
  | ISNUM { IsNum }
  | ISTUPLE { IsTuple }
  | PRINTSTACK { PrintStack }

bindings :
  | bind EQUAL expr { [($1, $3, (Parsing.rhs_start_pos 1, Parsing.rhs_end_pos 1))] }
  | bind EQUAL expr COMMA bindings { ($1, $3, (Parsing.rhs_start_pos 1, Parsing.rhs_end_pos 1))::$5 }

expr :
  | LET bindings IN expr { ELet($2, $4, (Parsing.symbol_start_pos (), Parsing.symbol_end_pos ())) }
  | IF expr COLON expr ELSECOLON expr { EIf($2, $4, $6, (Parsing.symbol_start_pos (), Parsing.symbol_end_pos ())) }
  | binop_expr SEMI expr { ESeq($1, $3, (Parsing.symbol_start_pos (), Parsing.symbol_end_pos ())) }
  | binop_expr { $1 }

exprs :
  | expr { [$1] }
  | expr COMMA exprs { $1::$3 }

tuple_expr :
  | LPARENNOSPACE RPAREN { ETuple([], (Parsing.symbol_start_pos (), Parsing.symbol_end_pos ())) }
  | LPARENSPACE RPAREN { ETuple([], (Parsing.symbol_start_pos (), Parsing.symbol_end_pos ())) }
  | LPARENNOSPACE expr COMMA RPAREN { ETuple([$2], (Parsing.symbol_start_pos (), Parsing.symbol_end_pos ())) }
  | LPARENSPACE expr COMMA RPAREN { ETuple([$2], (Parsing.symbol_start_pos (), Parsing.symbol_end_pos ())) }
  | LPARENNOSPACE expr COMMA exprs RPAREN { ETuple($2::$4, (Parsing.symbol_start_pos (), Parsing.symbol_end_pos ())) }
  | LPARENSPACE expr COMMA exprs RPAREN { ETuple($2::$4, (Parsing.symbol_start_pos (), Parsing.symbol_end_pos ())) }

tuple_get :
  | id LBRACK NUM OF NUM RBRACK { EGetItem($1, $3, $5, (Parsing.symbol_start_pos (), Parsing.symbol_end_pos ())) }
  | tuple_get LBRACK NUM OF NUM RBRACK { EGetItem($1, $3, $5, (Parsing.symbol_start_pos (), Parsing.symbol_end_pos ())) }

tuple_set :
  | id LBRACK NUM OF NUM COLONEQ expr RBRACK { ESetItem($1, $3, $5, $7, (Parsing.symbol_start_pos (), Parsing.symbol_end_pos ())) }
  | tuple_get LBRACK NUM OF NUM COLONEQ expr RBRACK { ESetItem($1, $3, $5, $7, (Parsing.symbol_start_pos (), Parsing.symbol_end_pos ())) }
  | tuple_set LBRACK NUM OF NUM COLONEQ expr RBRACK { ESetItem($1, $3, $5, $7, (Parsing.symbol_start_pos (), Parsing.symbol_end_pos ())) }


simple_expr :
  // Primops
  | prim1 LPARENNOSPACE expr RPAREN { EPrim1($1, $3, (Parsing.symbol_start_pos (), Parsing.symbol_end_pos ())) }
  // Tuples
  | tuple_expr { $1 }
  | tuple_get { $1 }
  | tuple_set { $1 }
  // Function calls
  | ID LPARENNOSPACE exprs RPAREN { EApp($1, $3, (Parsing.symbol_start_pos (), Parsing.symbol_end_pos ())) }
  | ID LPARENNOSPACE RPAREN { EApp($1, [], (Parsing.symbol_start_pos (), Parsing.symbol_end_pos ())) }
  // Parentheses
  | LPARENSPACE expr RPAREN { $2 }
  | LPARENNOSPACE expr RPAREN { $2 }
  // Simple cases
  | const { $1 }
  | id { $1 }

id :
  | ID %prec COLON { EId($1, (Parsing.symbol_start_pos (), Parsing.symbol_end_pos ())) }
  | LPARENNOSPACE ID COLON typ RPAREN { EAnnot(EId($2, (Parsing.rhs_start_pos 2, Parsing.rhs_end_pos 2)), $4,
                                               (Parsing.symbol_start_pos (), Parsing.symbol_end_pos ())) }
  | LPARENSPACE ID COLON typ RPAREN { EAnnot(EId($2, (Parsing.rhs_start_pos 2, Parsing.rhs_end_pos 2)), $4,
                                             (Parsing.symbol_start_pos (), Parsing.symbol_end_pos ())) }


binop_expr :
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
  | simple_expr { $1 }

decl :
  | DEF ID LPARENNOSPACE RPAREN COLON expr
    { let arg_pos = Parsing.rhs_start_pos 3, Parsing.rhs_end_pos 4 in
      DFun($2, [], SForall([], TyArr([], TyBlank arg_pos, arg_pos), arg_pos), $6, (Parsing.symbol_start_pos (), Parsing.symbol_end_pos ())) }
  | DEF ID LPARENNOSPACE RPAREN THINARROW typ COLON expr
    {
      let typ_pos = (Parsing.rhs_start_pos 6, Parsing.rhs_end_pos 6) in
      DFun($2, [], SForall([], TyArr([], $6, typ_pos), typ_pos), $8, (Parsing.symbol_start_pos (), Parsing.symbol_end_pos ())) }
  | DEF ID LESSNOSPACE tyids GREATER LPARENNOSPACE binds RPAREN THINARROW typ COLON expr
    {
      let arg_types = List.map bind_to_typ $7 in
      let arrow_pos = (Parsing.rhs_start_pos 6, Parsing.rhs_end_pos 10) in
      let typ_pos = (Parsing.rhs_start_pos 3, Parsing.rhs_end_pos 10) in
      DFun($2, $7, SForall($4, TyArr(arg_types, $10, arrow_pos), typ_pos), $12, (Parsing.symbol_start_pos (), Parsing.symbol_end_pos ()))
    }
  | DEF ID LPARENNOSPACE binds RPAREN COLON expr
    {
      let arg_types = List.map bind_to_typ $4 in
      let typ_pos = (Parsing.rhs_start_pos 3, Parsing.rhs_end_pos 5) in
      let arr_typ = SForall([], TyArr(arg_types, TyBlank(typ_pos), typ_pos), typ_pos) in
      DFun($2, $4, arr_typ, $7, (Parsing.symbol_start_pos (), Parsing.symbol_end_pos ()))
    }
  | DEF ID LPARENNOSPACE binds RPAREN THINARROW typ COLON expr
    {
      let arg_types = List.map bind_to_typ $4 in
      let typ_pos = (Parsing.rhs_start_pos 3, Parsing.rhs_end_pos 7) in
      DFun($2, $4, SForall([], TyArr(arg_types, $7, typ_pos), typ_pos), $9, (Parsing.symbol_start_pos (), Parsing.symbol_end_pos ()))
    }

tyids :
  | { [] }
  | TYID { [$1] }
  | TYID COMMA tyids { $1::$3 }

tyid : TYID { TyVar($1, (Parsing.symbol_start_pos (), Parsing.symbol_end_pos ())) }

binds :
  | bind { [$1] }
  | bind COMMA binds { $1::$3 }

bind :
  | ID { BName($1, TyBlank(Parsing.symbol_start_pos (), Parsing.symbol_end_pos ()), (Parsing.symbol_start_pos (), Parsing.symbol_end_pos ())) }
  | ID COLON typ { BName($1, $3, (Parsing.symbol_start_pos (), Parsing.symbol_end_pos ())) }
  | LPARENNOSPACE binds RPAREN { BTuple($2, (Parsing.symbol_start_pos (), Parsing.symbol_end_pos ())) }
  | LPARENSPACE binds RPAREN { BTuple($2, (Parsing.symbol_start_pos (), Parsing.symbol_end_pos ())) }

typ :
  | ID { TyCon($1, (Parsing.symbol_start_pos (), Parsing.symbol_end_pos ())) }
  | tyid { $1 }
  | arrowtyp { $1 }
  | tupletyp { $1 }

arrowtyp :
  | LPARENNOSPACE typs THINARROW typ RPAREN { TyArr($2, $4, (Parsing.symbol_start_pos (), Parsing.symbol_end_pos ())) }
  | LPARENSPACE typs THINARROW typ RPAREN { TyArr($2, $4, (Parsing.symbol_start_pos (), Parsing.symbol_end_pos ())) }

tupletyp :
  | LPARENNOSPACE startyps RPAREN { TyTup($2, (Parsing.symbol_start_pos (), Parsing.symbol_end_pos ())) }
  | LPARENSPACE startyps RPAREN { TyTup($2, (Parsing.symbol_start_pos (), Parsing.symbol_end_pos ())) }


typs :
  | typ { [$1] }
  | typ COMMA typs { $1::$3 }

startyps :
  | typ { [$1] }
  | typ TIMES startyps { $1::$3 }

declgroup :
  | decl { [$1] }
  | decl ANDDEF declgroup { $1::$3 }

decls :
  | { [] }
  | declgroup decls { $1::$2 }

tydecl :
  | TYPE ID EQUAL LPARENNOSPACE startyps RPAREN { TyDecl($2, $5, (Parsing.symbol_start_pos (), Parsing.symbol_end_pos())) }
  | TYPE ID EQUAL LPARENSPACE startyps RPAREN { TyDecl($2, $5, (Parsing.symbol_start_pos (), Parsing.symbol_end_pos())) }

tydecls :
  | { [] }
  | tydecl tydecls { $1 :: $2 }

program :
  | tydecls decls expr EOF { Program($1, $2, $3, (Parsing.symbol_start_pos (), Parsing.symbol_end_pos ())) }

%%
