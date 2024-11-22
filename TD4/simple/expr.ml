type tvar = string
(** Type variables. *)

type var = string
(** Term variables. *)

(** Types. Either a simple type of a function type. 
    Extensions: conjunction, disjunction, truth, falsity
 *)
type ty =
  | TVar of tvar
  | Imp of ty * ty
  | And of ty * ty
  | Or of ty * ty
  | True
  | False

let neg ty = Imp (ty, False)

(** Terms. A variable, a function application, or a lambda abstraction. 
    Extensions: pair (conjunction), left/right (disjunction), one (unit)
 *)
type tm =
  | Var of var
  | App of tm * tm
  | Abs of var * ty * tm
  | Pair of tm * tm
  | Fst of tm
  | Snd of tm
  | Left of tm * ty
  | Right of ty * tm
  | Case of tm * var * tm * var * tm
  | Unit
  | Absurd of tm * ty

type context = (var * ty) list
(** Environments. *)

let rec string_of_ty = function
  | TVar t -> t
  | Imp (dom, codom) ->
      "(" ^ string_of_ty dom ^ " => " ^ string_of_ty codom ^ ")"
  | And (t1, t2) -> "(" ^ string_of_ty t1 ^ " /\\ " ^ string_of_ty t2 ^ ")"
  | Or (t1, t2) -> "(" ^ string_of_ty t1 ^ " \\/ " ^ string_of_ty t2 ^ ")"
  | True -> "T"
  | False -> "_"

let rec string_of_tm = function
  | Var x -> x
  | App (t, u) -> "(" ^ string_of_tm t ^ " " ^ string_of_tm u ^ ")"
  | Abs (x, a, t) ->
      "(fun (" ^ x ^ " : " ^ string_of_ty a ^ ") -> " ^ string_of_tm t ^ ")"
  | Pair (fst, snd) -> "(" ^ string_of_tm fst ^ ", " ^ string_of_tm snd ^ ")"
  | Fst t -> "fst(" ^ string_of_tm t ^ ")"
  | Snd t -> "snd(" ^ string_of_tm t ^ ")"
  | Left (t, _b) -> "left(" ^ string_of_tm t ^ ")"
  | Right (_a, t) -> "right(" ^ string_of_tm t ^ ")"
  | Case (disj, x, l, y, r) ->
      "case " ^ string_of_tm disj ^ " of " ^ x ^ " -> " ^ string_of_tm l ^ "|"
      ^ y ^ " -> " ^ string_of_tm r
  | Unit -> "()"
  | Absurd (e, t) -> "absurd(" ^ string_of_tm e ^ ", " ^ string_of_ty t ^ ")"
