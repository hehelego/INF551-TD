type var = string [@@deriving show { with_path = false }]
(** Variables. *)

let fresh_var : unit -> string =
  let c = ref 0 in
  fun () ->
    let n = !c + 1 in
    c := n;
    "!" ^ string_of_int n

let unused : var = "*"

(** Expressions. *)
type expr =
  | Type  (** type universe *)
  (* functions *)
  | Var of var  (** binder *)
  | App of expr * expr  (** App : (f : (x : A) -> B x) (x : A) -> B x *)
  | Abs of var * expr * expr  (** lambda (x : t) u *)
  | Pi of var * expr * expr  (** Pi (x : t) A *)
  (* natural number *)
  | Nat  (** Nat type *)
  | Z  (** Z: Nat *)
  | S of expr  (** S: Nat -> Nat *)
  | Ind of expr * expr * expr * expr
      (** Ind: (P : Nat -> Type) -> P Z -> (Pi (n : Nat) n -> P n -> P (S n)) ->
          (n : Nat) -> P n *)
  (* equality *)
  | Eq of expr * expr  (** Eq : {A : Type} (a b : A) -> Type *)
  | Refl of expr  (** Refl {A : Type} (a : A) -> Eq a a *)
  | J of expr * expr * expr * expr * expr
      (**
         J: {A : Type} ->
             (P : (x y : A) -> x = y -> Type) ->
                 (r : (t : A) -> P t t (Refl t)) ->
                     (x y : A) -> x = y -> P x y
              *)
  (* true/false and negation *)
  | True  (** True: Type *)
  | Unit  (** Unit: True *)
  | False  (** False: Type *)
  | Absurd of expr * expr  (** Absurd: False -> (A : Type) -> A *)
  (* coproduct / dependent pairs *)
  | Sigma of var * expr * expr  (** Sigma: Sigma (x : A) B *)
  | Pair of expr * expr * expr
      (** Pair: {A : Type} (x : A) (B : A -> Type) (y : B x) -> Sigma (x : A) (B x) *)
  | Fst of expr
      (** Fst : {A : Type} {B : A -> Type} -> Sigma (x : A) (B x) -> A *)
  | Snd of expr
      (** Snd : {A : Type} {B : A -> Type} -> (p : Sigma (x : A) (B x)) -> B (fst p) *)
  (* list *)
  | List of expr  (** List: Type -> Type *)
  | Nil of expr  (** nil: (A : Type) -> List A *)
  | Cons of expr * expr  (** cons: (A : Type) -> A -> List A -> List A *)
  | Rec of expr * expr * expr * expr
      (** Rec: {A : Type} (P : List A -> Type) ->
          P [] ->
              (Pi (x : A) -> Pi (l : List A) -> P l -> P (x :: l)) ->
                  (l : List A) -> P l *)
  (* conjunction and disjunction *)
  | Conj of expr * expr  (** Conj: Type -> Type -> Type *)
  | And of expr * expr  (** And: {A B : Type} (x : A) (y : B) -> Conj A B *)
  | Proj0 of expr  (** {A B : Type} -> Disj A B -> A *)
  | Proj1 of expr  (** {A B : Type} -> Disj A B -> B *)
  | Disj of expr * expr  (** Disj: Type -> Type -> Type *)
  | Or0 of expr * expr  (** Or0: {A : Type} (x : A) (B : Type) -> Disj A B *)
  | Or1 of expr * expr  (** Or1: {B : Type} (y : B) (A : Type) -> Disj A B *)
  | Case of expr * expr * expr
      (** Case: {A B C : Type} (p : Disj A B) (f : A -> C) (g : B -> C) -> C *)
[@@deriving show { with_path = false }]

let impl a b =
  let v = fresh_var () in
  Pi (v, a, b)

let neg x =
  let v = fresh_var () in
  Pi (v, x, False)

type context = (var * (expr * expr option)) list
[@@deriving show { with_path = false }]
