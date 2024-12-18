type var = string [@@deriving show { with_path = false }]
(** Variables. *)

(** Expressions. *)
type expr =
  (* type universe *)
  | Type
  (* functions *)
  | Var of var
  | App of expr * expr
  | Abs of var * expr * expr
  | Pi of var * expr * expr
  (* natural number *)
  | Nat
  | Z
  | S of expr
  | Ind of expr * expr * expr * expr
  (* equality *)
  | Eq of expr * expr
  | Refl of expr
  | J of expr * expr * expr * expr * expr
  (* conjunction *)
  | Conj of expr * expr
  | Pair of expr * expr
  | Proj0 of expr
  | Proj1 of expr
  (* disjunction *)
  | Disj of expr * expr
  | Inj0 of expr * expr
  | Inj1 of expr * expr
  | Case of expr * expr * expr
  (* true/false and negation *)
  | True
  | False
  | Unit
  | Absurd of expr * expr
[@@deriving show { with_path = false }]

let impl a b = Pi ("_", a, b)
let neg x = Pi ("_", x, False)

type context = (var * (expr * expr option)) list
[@@deriving show { with_path = false }]
