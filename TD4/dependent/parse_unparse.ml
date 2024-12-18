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
  | Pi (x, t, u) ->
      if x = "_" then fmt "(%s => %s)" (to_string t) (to_string u)
      else fmt "(Pi (%s : %s) -> %s)" x (to_string t) (to_string u)
  (* natrual numbers *)
  | Nat -> "Nat"
  | Z -> "Z"
  | S n -> fmt "(S %s)" (to_string n)
  | Ind (p, base, step, n) ->
      fmt "(Ind %s %s %s %s)" (to_string p) (to_string base) (to_string step)
        (to_string n)
  (* equality types *)
  | Eq (t, u) -> fmt "(%s = %s)" (to_string t) (to_string u)
  | Refl e -> fmt "(Refl %s)" (to_string e)
  | J (p, p_refl, x, y, eq) ->
      fmt "(J %s %s %s %s %s)" (to_string p) (to_string p_refl) (to_string x)
        (to_string y) (to_string eq)
  (* conjunction *)
  | Conj (u, v) -> fmt "(%s /\\ %s)" (to_string u) (to_string v)
  | Pair (u, v) -> fmt "(Pair %s %s)" (to_string u) (to_string v)
  | Proj0 t -> fmt "(Proj0 %s)" (to_string t)
  | Proj1 t -> fmt "(Proj1 %s)" (to_string t)
  (* disjunction *)
  | Disj (u, v) -> fmt "(%s \\/ %s)" (to_string u) (to_string v)
  | Inj0 (x, tyR) -> fmt "(Inj0 %s | %s)" (to_string x) (to_string tyR)
  | Inj1 (tyL, y) -> fmt "(Inj1 %s | %s)" (to_string tyL) (to_string y)
  | Case (t, l, r) ->
      fmt "(Case %s of %s | %s)" (to_string t) (to_string l) (to_string r)
  (* true/false and negation *)
  | True -> "True"
  | False -> "False"
  | Unit -> "()"
  | Absurd (bot, ty) -> fmt "(bot-elim %s : %s)" (to_string bot) (to_string ty)

let string_of_context (ctx : context) : string =
  ctx
  |> List.map (fun (x, (ty, _)) ->
         let str_ty = to_string ty in
         fmt "%s : %s" x str_ty)
  |> String.concat "\n"

let%test "parse and 1" = of_string "A /\\ B" = Conj (Var "A", Var "B")

let%test "parse and 2" =
  of_string "A /\\ B /\\ C" = Conj (Conj (Var "A", Var "B"), Var "C")

let%test "parse or 1" = of_string "A \\/ B" = Disj (Var "A", Var "B")

let%test "parse or 2" =
  of_string "A \\/ B \\/ C" = Disj (Disj (Var "A", Var "B"), Var "C")

let%test "parse not 1" = of_string "~ A" = (Var "A" |> neg)
let%test "parse not 2" = of_string "~ ~ A" = (Var "A" |> neg |> neg)
let%test "parse not 3" = of_string "~ ~ ~ A" = (Var "A" |> neg |> neg |> neg)
let%test "parser impl 1" = of_string "A => B" = impl (Var "A") (Var "B")

let%test "parser impl 2" =
  of_string "A => B => C" = impl (Var "A") (impl (Var "B") (Var "C"))

let%test "parser not-impl" =
  of_string "~A => B" = impl (Var "A" |> neg) (Var "B")

let%test "parse and-or" =
  of_string "A /\\ B \\/ C /\\ D"
  = Disj (Conj (Var "A", Var "B"), Conj (Var "C", Var "D"))

let%test "parse or-and-imp-last" =
  let head = Disj (Conj (Var "A", Var "B"), Conj (Var "C", Var "D")) in
  let tail = Var "X" in
  of_string "A /\\ B \\/ C /\\ D => X" = impl head tail

let%test "parse and-imp-and" =
  let head = Conj (Var "A", Var "B") in
  let tail = Conj (Var "C", Var "D") in
  of_string "A /\\ B => C /\\ D" = impl head tail

let%test "parse or-imp-or" =
  let head = Disj (Var "A", Var "B") in
  let tail = Disj (Var "C", Var "D") in
  of_string "A \\/ B => C \\/ D" = impl head tail

let%test "parse and-or-imp" =
  let head = Conj (Var "A", Var "B") in
  let tail = Disj (Var "C", Var "D") in
  of_string "A /\\ B => C \\/ D" = impl head tail

let%test "parse complex" =
  let a, b = (Var "A", Var "B") in
  let body = Conj (impl a b, impl b a) in
  let quantified = Pi ("A", Type, Pi ("B", Type, body)) in
  of_string "Pi (A : Type) -> Pi (B : Type) -> (A => B) /\\ (B => A)"
  = quantified

let%test "parse not-and 0" =
  of_string "~ ~ A /\\ B" = Conj (Var "A" |> neg |> neg, Var "B")

let%test "parse not-and 1" =
  of_string "~ ~ A /\\ ~ B" = Conj (Var "A" |> neg |> neg, Var "B" |> neg)

let%test "parse not-or 1" =
  of_string "~ A \\/ ~ B" = Disj (Var "A" |> neg, Var "B" |> neg)

let%test "parser inj0" =
  let _ = of_string "Inj0 (Pair (fst aBC) b) (A /\\ C)" in
  let _ = of_string "Inj1 (A /\\ B) (Pair (fst aBC) c)" in
  true
