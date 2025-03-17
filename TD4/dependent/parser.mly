%{
open Expr
%}

%token IMP
%token OR0 OR1 CASE
%token PAIR FST SND
%token TRUE FALSE UNIT ABSURD
%token PI SIGMA
%token TYPE
%token NAT Z S IND
%token EQ REFL J
%token LIST NIL CONS REC
%token TO FUN
%token NOT CONJ DISJ AND OR PROJ0 PROJ1
%token LPAR RPAR COLON COMMA
%token <string> IDENT
%token EOF

%nonassoc EQ
%right IMP
%left CONJ
%left DISJ

%start expr
%type <Expr.expr> expr
%%

/* Precedences:
    (highest)
    ~
    =
    /\
    \/
    =>
    (lowest)
*/

/* An expression */
expr:
  | implexpr                               { $1 }
  | PI LPAR IDENT COLON expr RPAR expr     { Pi ($3, $5, $7) }
  | LPAR IDENT COLON expr RPAR TO expr     { Pi ($2, $4, $7) }
  | SIGMA LPAR IDENT COLON expr RPAR expr  { Sigma ($3, $5, $7) }
  | FUN LPAR IDENT COLON expr RPAR TO expr { Abs ($3, $5, $8) }

/* a binary expression whose top level operator is logical-implication */
implexpr:
  | orexpr                                 { $1 }
  | orexpr IMP implexpr                    { impl $1 $3 }

/* a binary expression whose top level operator is logical-or */
orexpr:
  | andexpr                                { $1 }
  | andexpr DISJ orexpr                    { Disj ($1, $3) }

/* a binary expression whose top level operator is logical-and */
andexpr:
  | eqexpr                                 { $1 }
  | eqexpr CONJ andexpr                    { Conj ($1, $3) }

/* a binary expression whose top level operator is equality */
eqexpr:
  | aexpr                                  { $1 }
  | aexpr EQ eqexpr                        { Eq ($1, $3) }

/* An application */
aexpr:
  | sexpr                                  { $1 }
  | aexpr sexpr                            { App ($1, $2) }

/* A simple expression */
sexpr:
  | LPAR expr RPAR                         { $2 }
  | IDENT                                  { Var $1 }
  | TYPE                                   { Type }
  (* natural numbers *)
  | NAT                                    { Nat }
  | Z                                      { Z }
  | S sexpr                                { S $2 }
  | IND sexpr sexpr sexpr sexpr            { Ind ($2, $3, $4, $5) }
  (* equality *)
  | REFL sexpr                             { Refl $2 }
  | J sexpr sexpr sexpr sexpr sexpr        { J ($2, $3, $4, $5, $6) }
  (* true/false and negation *)
  | TRUE                                   { True }
  | FALSE                                  { False }
  | UNIT                                   { Unit }
  | ABSURD sexpr sexpr                     { Absurd ($2, $3) }
  | NOT sexpr                              { neg $2 }
  (* coproduct *)
  | PAIR sexpr sexpr sexpr                 { Pair ($2, $3, $4) }
  | FST sexpr                              { Fst $2 }
  | SND sexpr                              { Snd $2 }
  (* list *)
  | LIST sexpr                             { List $2 }
  | NIL sexpr                              { Nil $2 }
  | CONS sexpr sexpr                       { Cons ($2, $3) }
  | REC sexpr sexpr sexpr sexpr            { Rec ($2, $3, $4, $5) }
  (* logical connectives and/or *)
  | AND sexpr sexpr                        { And ($2, $3) }
  | PROJ0 sexpr                            { Proj0 $2 }
  | PROJ1 sexpr                            { Proj1 $2 }
  | OR0 sexpr sexpr                        { Or0 ($2, $3) }
  | OR1 sexpr sexpr                        { Or1 ($2, $3) }
  | CASE sexpr sexpr sexpr                 { Case ($2, $3, $4) }

