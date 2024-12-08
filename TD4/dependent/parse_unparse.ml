open Expr

let of_string s = Parser.expr Lexer.token (Lexing.from_string s)
let fmt = Printf.sprintf

(** string representation of a term *)
let rec to_string : expr -> string = function
  (* type universe *)
  | Type -> "Type"
  (* function terms *)
  | Var x -> x
  | App (t, u) -> fmt "(%s %s)" (to_string t) (to_string u)
  | Abs (x, t, u) -> fmt "(fun (%s : %s) -> %s)" x (to_string t) (to_string u)
  (* dependent function type *)
  | Pi (x, t, u) -> fmt "(Pi (%s : %s) -> %s)" x (to_string t) (to_string u)
  (* natrual numbers *)
  | Nat -> "Nat"
  | Z -> "Z"
  | S n -> fmt "(S %s)" (to_string n)
  | Ind _ -> assert false
  (* equality types *)
  | Eq (t, u) -> fmt "(%s = %s)" (to_string t) (to_string u)
  | Refl e -> fmt "(refl %s)" (to_string e)
  | J _ -> assert false
