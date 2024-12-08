open Expr
open Parse_unparse

exception Type_error of string

let fresh_var : unit -> string =
  let c = ref 0 in
  fun () ->
    let n = !c + 1 in
    c := n;
    fmt "z%d" n

(** [free_var x t] test whether [x] occurs freely in [t] *)
let rec free_var (x : var) : expr -> bool = function
  | Type -> false
  | Var y -> x = y
  | App (u, v) -> free_var x u || free_var x v
  (* Consider the following corner case
     Pi(x : A) . ( Pi(x : F(x)) . B(x) ) *)
  | Abs (y, t, u) -> free_var x t || (x <> y && free_var x u)
  | Pi (y, t, u) -> free_var x t || (x <> y && free_var x u)
  | Nat -> false
  | Z -> false
  | S n -> free_var x n
  | Ind _ -> assert false
  | Eq (t, u) -> free_var x t || free_var x u
  | Refl e -> free_var x e
  | J _ -> assert false

(** [subst x t u] replaces all free occurence of [x] in [u] with [t] *)
let rec subst (x : var) (tm : expr) : expr -> expr = function
  | Type -> Type
  | Var y -> if x = y then tm else Var y
  | App (u, v) ->
      let u' = subst x tm u in
      let v' = subst x tm v in
      App (u', v')
  | Abs (y, ty, u) ->
      let ty' = subst x tm ty in
      if x = y then Abs (y, ty', u)
      else if free_var y tm then
        let y' = fresh_var () in
        let u' = subst y (Var y') u in
        Abs (y', ty', subst x tm u')
      else Abs (y, ty', subst x tm u)
  | Pi (y, ty, u) ->
      let ty' = subst x tm ty in
      if x = y then Abs (y, ty', u)
      else if free_var y tm then
        let y' = fresh_var () in
        let u' = subst y (Var y') u in
        Pi (y', ty', subst x tm u')
      else Pi (y, ty', subst x tm u)
  (* natrual numbers *)
  | Nat -> Nat
  | Z -> Z
  | S n -> S (subst x tm n)
  | Ind _ -> assert false
  (* (* equality types *) *)
  | Eq (t, u) ->
      let t' = subst x tm t in
      let u' = subst x tm u in
      Eq (t', u')
  | Refl e -> Refl (subst x tm e)
  | J _ -> assert false

let string_of_context (ctx : context) : string =
  ctx
  |> List.map (fun (x, (ty, _)) ->
         let str_ty = to_string ty in
         fmt "%s : %s" x str_ty)
  |> String.concat "\n"

(** Reducing a term one step further if it is possible.
    Precondition: the input term is well-typed and have no free variable not in the context
 *)
let rec reduce (ctx : context) : expr -> expr option = function
  | Type -> None
  | Var x -> (
      match List.assoc_opt x ctx with
      | Some (_ty, value) -> value
      | None -> raise (Type_error (fmt "%s not in scope in reduction" x)))
  | App (Abs (x, _t, u), v) -> Some (subst x v u)
  | App (Pi (x, _t, u), v) -> Some (subst x v u)
  | App (t, u) -> (
      match reduce ctx t with
      | Some t' -> Some (App (t', u))
      | None -> (
          match reduce ctx u with Some u' -> Some (App (t, u')) | None -> None))
  | Abs (x, t, u) -> (
      match reduce ctx t with
      | Some t' -> Some (Abs (x, t', u))
      | None -> (
          let ctx' = (x, (t, None)) :: ctx in
          match reduce ctx' u with
          | Some u' -> Some (Abs (x, t, u'))
          | None -> None))
  (* dependent function type *)
  | Pi (x, t, u) -> (
      match reduce ctx t with
      | Some t' -> Some (Pi (x, t', u))
      | None -> (
          let ctx' = (x, (t, None)) :: ctx in
          match reduce ctx' u with
          | Some u' -> Some (Pi (x, t, u'))
          | None -> None))
  | Nat -> None
  | Z -> None
  | S n -> ( match reduce ctx n with Some n' -> Some (S n') | None -> None)
  | Ind _ -> assert false
  | Eq (t, u) -> (
      match reduce ctx t with
      | Some t' -> Some (Eq (t', u))
      | None -> (
          match reduce ctx u with Some u' -> Some (Eq (t, u')) | None -> None))
  | Refl e -> (
      match reduce ctx e with Some e' -> Some (Refl e') | None -> None)
  | J _ -> assert false

(** Normalizing a term by repeatedly reducing it
 NOTE: this function may not terminate *)
let rec normalize (ctx : context) (t : expr) : expr =
  match reduce ctx t with Some t' -> normalize ctx t' | None -> t

(** test if two terms are equivalent up-to alpha-renaming *)
let rec alpha (tm : expr) (tm' : expr) : bool =
  match (tm, tm') with
  | Type, Type -> true
  | Var x, Var y -> x = y
  | App (t, u), App (t', u') -> alpha t t' && alpha u u'
  | Abs (x, t, u), Abs (y, t', u') ->
      alpha t t'
      &&
      let z = Var (fresh_var ()) in
      let v, v' = (subst x z u, subst y z u') in
      alpha v v'
  | Pi (x, t, u), Pi (y, t', u') ->
      alpha t t'
      &&
      let z = Var (fresh_var ()) in
      let v, v' = (subst x z u, subst y z u') in
      alpha v v'
  | _ -> false

(** test whether two terms are alpha-beta convertible under a context *)
let conv (ctx : context) (t : expr) (t' : expr) : bool =
  let t = normalize ctx t in
  let t' = normalize ctx t' in
  alpha t t'

let check_conv (ctx : context) (t : expr) (t' : expr) : unit =
  if conv ctx t t' then ()
  else
    let st, st' = (to_string t, to_string t') in
    raise (Type_error (fmt "%s =/= %s in the given context" st st'))

let rec infer (ctx : context) : expr -> expr = function
  | Type -> Type
  | Var v -> (
      match List.assoc_opt v ctx with
      | Some (ty, _) -> ty
      | None -> raise (Type_error (fmt "variable %s not in context" v)))
  | App (t, u) -> (
      match infer ctx t with
      | Pi (x, arg, ret) ->
          check ctx u arg;
          subst x u ret
      | ty ->
          raise
            (Type_error (fmt "expecting a function, found %s" (to_string ty))))
  | Abs (x, arg, ret) ->
      let ctx' = (x, (arg, None)) :: ctx in
      let ret' = infer ctx' ret in
      Pi (x, arg, ret')
  | Pi (x, arg, ret) ->
      check_typable ctx arg;
      let ctx' = (x, (arg, None)) :: ctx in
      check_typable ctx' ret;
      Type
  | Nat -> Type
  | Z -> Nat
  | S n ->
      check ctx n Nat;
      Nat
  | Ind _ -> assert false
  | Eq (t, u) ->
      let tt = infer ctx t in
      let tu = infer ctx u in
      check_conv ctx tt tu;
      Type
  | Refl e ->
      check_typable ctx e;
      Eq (e, e)
  | J _ -> assert false

and check (ctx : context) (tm : expr) (ty : expr) : unit =
  let ty' = infer ctx tm in
  check_conv ctx ty ty'

and check_typable (ctx : context) (tm : expr) : unit =
  let _ = infer ctx tm in
  ()
