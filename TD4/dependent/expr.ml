type var = string [@@deriving show { with_path = false }]
(** Variables. *)

(** Expressions. *)
type expr =
  (* the universe *)
  | Type
  (* function terms *)
  | Var of var
  | App of expr * expr
  | Abs of var * expr * expr
  (* function type *)
  | Pi of var * expr * expr
  (* natural numbers *)
  | Nat
  | Z
  | S of expr
  | Ind of expr * expr * expr * expr
  (* equality types *)
  | Eq of expr * expr
  | Refl of expr
  | J of expr * expr * expr * expr * expr
[@@deriving show { with_path = false }]

type context = (var * (expr * expr option)) list
[@@deriving show { with_path = false }]
