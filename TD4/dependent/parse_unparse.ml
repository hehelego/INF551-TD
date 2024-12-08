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
  | Ind (p, base, step, n) ->
      fmt "(Ins %s %s %s %s)" (to_string p) (to_string base) (to_string step)
        (to_string n)
  (* equality types *)
  | Eq (t, u) -> fmt "(%s = %s)" (to_string t) (to_string u)
  | Refl e -> fmt "(Refl %s)" (to_string e)
  | J (p, p_refl, x, y, eq) ->
      fmt "(J %s %s %s %s %s)" (to_string p) (to_string p_refl) (to_string x)
        (to_string y) (to_string eq)

let string_of_context (ctx : context) : string =
  ctx
  |> List.map (fun (x, (ty, _)) ->
         let str_ty = to_string ty in
         fmt "%s : %s" x str_ty)
  |> String.concat "\n"
