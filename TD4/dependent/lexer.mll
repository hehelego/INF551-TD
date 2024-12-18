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
  | "/\\"    { AND }
  | "Pair"   { PAIR }
  | "Proj0"  { PROJ0 }
  | "Proj1"  { PROJ1 }
  | "\\/"    { OR }
  | "Inj0"   { INJ0 }
  | "Inj1"   { INJ1 }
  | "Case"   { CASE }
  | "~"      { NOT }
  | "True"   { TRUE }
  | "Unit"   { UNIT }
  | "False"  { FALSE }
  | "Absurd" { ABSURD }
  | (['A'-'Z''a'-'z''0'-'9']+ as s) { IDENT s }
  | space+ { token lexbuf }
  | '#'([^'#']*'\n') { token lexbuf }
  | "\n" { new_line lexbuf; token lexbuf }
  | eof { EOF }
