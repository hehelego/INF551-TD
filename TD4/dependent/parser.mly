%{
open Expr
%}

%token IMP
%token OR
%token AND
%token NOT
%token INJ0 INJ1 CASE
%token PAIR PROJ0 PROJ1
%token TRUE FALSE UNIT ABSURD
%token PI TYPE NAT Z S IND EQ REFL J
%token TO FUN
%token LPAR RPAR COLON COMMA
%token <string> IDENT
%token EOF

%nonassoc EQ
%right IMP
%left OR
%left AND
%right NOT

%start expr
%type <Expr.expr> expr
%%

/* Precedences:
    (highest)
    !
    =
    /\
    \/
    =>
    (lowest)
*/

/* An expression */
expr:
  | implexpr                               { $1 }
  | PI LPAR IDENT COLON expr RPAR TO expr  { Pi ($3, $5, $8) }
  | LPAR IDENT COLON expr RPAR TO expr     { Pi ($2, $4, $7) }
  | FUN LPAR IDENT COLON expr RPAR TO expr { Abs ($3, $5, $8) }

/* a binary expression whose top level operator is logical-implication */
implexpr:
  | orexpr                                 { $1 }
  | orexpr IMP implexpr                    { Pi ("_", $1, $3) }

/* a binary expression whose top level operator is logical-or */
orexpr:
  | andexpr                                { $1 }
  | orexpr OR andexpr                     { Disj ($1, $3) }

/* a binary expression whose top level operator is logical-and */
andexpr:
  | eqexpr                                 { $1 }
  | andexpr AND eqexpr                      { Conj ($1, $3) }

/* a binary expression whose top level operator is equality */
eqexpr:
  | aexpr                                  { $1 }
  | aexpr EQ aexpr                         { Eq ($1, $3) }

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
  (* conjunction *)
  | PAIR sexpr sexpr                       { Pair ($2, $3) }
  | PROJ0 sexpr                            { Proj0 $2 }
  | PROJ1 sexpr                            { Proj1 $2 }
  (* disjunction *)
  | INJ0 sexpr sexpr                       { Inj0 ($2, $3) }
  | INJ1 sexpr sexpr                       { Inj1 ($2, $3) }
  | CASE sexpr sexpr sexpr                 { Case ($2, $3, $4) }
  (* true/false and negation *)
  | TRUE                                   { True }
  | FALSE                                  { False }
  | UNIT                                   { Unit }
  | ABSURD sexpr sexpr                     { Absurd ($2, $3) }
  | NOT sexpr                              { Pi ("_", $2, False) }
