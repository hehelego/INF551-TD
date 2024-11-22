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

type sequent = context * ty
(** A sequent is of the form
    Gamma |- A
    where Gamma is a list of assumptions and A is a formula
    *)

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

let string_of_ctx ctx =
  let type_label (x, a) = x ^ " : " ^ string_of_ty a in
  ctx |> List.map type_label |> String.concat " , "

let string_of_seq (ctx, ty) = string_of_ctx ctx ^ " |- " ^ string_of_ty ty

let%test_unit "string_ctx" =
  let ctx =
    [
      ("x", Imp (TVar "A", TVar "B"));
      ("y", And (TVar "A", TVar "B"));
      ("Z", TVar "T");
    ]
  in
  print_endline (string_of_ctx ctx);
  let str = "x : (A => B) , y : (A /\\ B) , Z : T" in
  assert (string_of_ctx ctx = str)

let%test_unit "string_seq" =
  let ctx = [ ("x", Imp (TVar "A", TVar "B")); ("y", TVar "A") ] in
  let seq = (ctx, TVar "B") in
  let str = "x : (A => B) , y : A |- B" in
  print_endline (string_of_seq seq);
  assert (string_of_seq seq = str)
