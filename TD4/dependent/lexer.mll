{
open Lexing
open Parser
}

let space = ' ' | '\t' | '\r'

rule token = parse
  | "fun"    { FUN }
  | "λ"      { FUN }
  | "Pi"     { PI }
  | "Π"      { PI }
  | "Type"   { TYPE }
  | "Nat"    { NAT }
  | "ℕ"      { NAT }
  | "Z"      { Z }
  | "S"      { S }
  | "Ind"    { IND }
  | "="      { EQ }
  | "≡"      { EQ }
  | "Refl"   { REFL }
  | "J"      { J }
  | "("      { LPAR }
  | ")"      { RPAR }
  | ":"      { COLON }
  | ","      { COMMA }
  | "->"     { TO }
  | "→"      { TO }
  | "=>"     { IMP }
  | "⇒"      { IMP }
  | "Sigma"  { SIGMA }
  | "Pair"   { PAIR }
  | "Fst"    { FST }
  | "Snd"    { SND }
  | "List"   { LIST }
  | "Nil"    { NIL }
  | "Cons"   { CONS }
  | "Rec"    { REC }
  | "True"   { TRUE }
  | "Unit"   { UNIT }
  | "False"  { FALSE }
  | "Absurd" { ABSURD }
  | "~"      { NOT }
  | "/\\"    { CONJ }
  | "\\/"    { DISJ }
  | "And"    { AND }
  | "Proj0"  { PROJ0 }
  | "Proj1"  { PROJ1 }
  | "Or0"    { OR0 }
  | "Or1"    { OR1 }
  | "Case"   { CASE }
  | (['A'-'Z''a'-'z''0'-'9''_']+ as s) { IDENT s }
  | space+ { token lexbuf }
  | '#'([^'#']*'\n') { token lexbuf }
  | "\n" { new_line lexbuf; token lexbuf }
  | eof { EOF }
