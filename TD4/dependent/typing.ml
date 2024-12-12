open Expr
open Parse_unparse

module Debug_runtime =
  Minidebug_runtime.PrintBox
    ((val Minidebug_runtime.shared_config "debugger_printbox.log"))

let () = Debug_runtime.config.values_first_mode <- true
let () = Printexc.record_backtrace true

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
  | Ind (p, z, s, n) ->
      free_var x p || free_var x z || free_var x s || free_var x n
  | Eq (t, u) -> free_var x t || free_var x u
  | Refl e -> free_var x e
  | J (p, p_refl, s, t, s_eq_t) ->
      free_var x p || free_var x p_refl || free_var x s || free_var x t
      || free_var x s_eq_t

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
        let z = fresh_var () in
        let u' = subst y (Var z) u in
        Abs (z, ty', subst x tm u')
      else Abs (y, ty', subst x tm u)
  | Pi (y, ty, u) ->
      let ty' = subst x tm ty in
      if x = y then Pi (y, ty', u)
      else if free_var y tm then
        let z = fresh_var () in
        let u' = subst y (Var z) u in
        Pi (z, ty', subst x tm u')
      else Pi (y, ty', subst x tm u)
  (* natrual numbers *)
  | Nat -> Nat
  | Z -> Z
  | S n -> S (subst x tm n)
  | Ind (p, z, s, n) ->
      let p' = subst x tm p in
      let z' = subst x tm z in
      let s' = subst x tm s in
      let n' = subst x tm n in
      Ind (p', z', s', n')
  (* (* equality types *) *)
  | Eq (t, u) ->
      let t' = subst x tm t in
      let u' = subst x tm u in
      Eq (t', u')
  | Refl e -> Refl (subst x tm e)
  | J (p, p_refl, s, t, eq) ->
      let p' = subst x tm p in
      let p_refl' = subst x tm p_refl in
      let s' = subst x tm s in
      let t' = subst x tm t in
      let eq' = subst x tm eq in
      J (p', p_refl', s', t', eq')

(** test if two terms are equivalent up-to alpha-renaming *)
let%track_show rec alpha (tm : expr) (tm' : expr) : bool =
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
  | Nat, Nat -> true
  | Z, Z -> true
  | S n, S n' -> alpha n n'
  | Ind (p, z, s, n), Ind (p', z', s', n') ->
      alpha p p' && alpha z z' && alpha s s' && alpha n n'
  | Eq (t, u), Eq (t', u') -> alpha t t' && alpha u u'
  | Refl e, Refl e' -> alpha e e'
  | J (p, r, x, y, eq), J (p', r', x', y', eq') ->
      alpha p p' && alpha r r' && alpha x x' && alpha y y' && alpha eq eq'
  | _ -> false

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
  | Ind (_p, z, _s, Z) -> Some z
  | Ind (p, z, s, S n) ->
      let ih = Ind (p, z, s, n) in
      Some (App (App (s, n), ih))
  | Ind (p, z, s, n) -> (
      match reduce ctx n with
      | Some n' -> Some (Ind (p, z, s, n'))
      | None -> None)
  | Eq (t, u) -> (
      match reduce ctx t with
      | Some t' -> Some (Eq (t', u))
      | None -> (
          match reduce ctx u with Some u' -> Some (Eq (t, u')) | None -> None))
  | Refl e -> (
      match reduce ctx e with Some e' -> Some (Refl e') | None -> None)
  | J (p, p_refl, s, t, eq) -> (
      match reduce ctx p with
      | Some p' -> Some (J (p', p_refl, s, t, eq))
      | None -> (
          match reduce ctx p_refl with
          | Some p_refl' -> Some (J (p, p_refl', s, t, eq))
          | None -> (
              match reduce ctx s with
              | Some s' -> Some (J (p, p_refl, s', t, eq))
              | None -> (
                  match reduce ctx t with
                  | Some t' -> Some (J (p, p_refl, s, t', eq))
                  | None -> (
                      match reduce ctx eq with
                      | Some eq' -> Some (J (p, p_refl, s, t, eq'))
                      | None ->
                          if alpha s t && alpha eq (Refl s) then
                            Some (App (p_refl, s))
                          else None)))))

(** Normalizing a term by repeatedly reducing it
 NOTE: this function may not terminate *)
let rec normalize (ctx : context) (t : expr) : expr =
  match reduce ctx t with Some t' -> normalize ctx t' | None -> t

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
      match infer ctx t |> normalize ctx with
      | Pi (x, arg, ret) ->
          check ctx u arg;
          subst x u ret
      | ty ->
          raise
            (Type_error (fmt "expecting a function, found %s" (to_string ty))))
  | Abs (x, arg, ret) ->
      check ctx arg Type;
      let ctx' = (x, (arg, None)) :: ctx in
      let ty_ret = infer ctx' ret in
      Pi (x, arg, ty_ret)
  | Pi (x, arg, ret) ->
      check ctx arg Type;
      let ctx' = (x, (arg, None)) :: ctx in
      check ctx' ret Type;
      Type
  | Nat -> Type
  | Z -> Nat
  | S n ->
      check ctx n Nat;
      Nat
  | Ind (p, z, s, n) -> (
      (*
      p : Nat -> Type
      z : p 0
      s : (n : Nat) -> (IH : p n) -> p (n + 1)
      n : Nat
      *)
      check ctx n Nat;
      match infer ctx p |> normalize ctx with
      | Pi (_x, Nat, Type) ->
          let p_z = App (p, Z) in
          check ctx z p_z;
          (* use a fresh variable to avoid capturing since [p] may contain free variable *)
          let y = fresh_var () in
          let p_n = App (p, Var y) in
          let p_sn = App (p, S (Var y)) in
          let ty_s_expect = Pi (y, Nat, Pi ("IH", p_n, p_sn)) in
          check ctx s ty_s_expect;

          App (p, n)
      | ty ->
          let msg = fmt "Ind expects a Nat -> Type. Actual %s" (to_string ty) in
          raise (Type_error msg))
  | Eq (t, u) ->
      let tt = infer ctx t in
      let tu = infer ctx u in
      check_conv ctx tt tu;
      Type
  | Refl e ->
      check_typable ctx e;
      Eq (e, e)
  | J (p, r, x, y, eq) ->
      let j_type x y eq = App (App (App (p, x), y), eq) in
      (* x and y are of the same type *)
      let a = infer ctx x in
      check ctx y a;
      (* p: (x y : A) -> x = y -> Type
         eq: x=y
         r: (x:A) -> p x x (Refl x) *)
      let s = fresh_var () in
      let t = fresh_var () in
      let vs, vt = (Var s, Var t) in
      let eq_pred = Pi ("_", Eq (vs, vt), Type) in
      check ctx p (Pi (s, a, Pi (t, a, eq_pred)));
      check ctx r (Pi (s, a, j_type vs vs (Refl vs)));
      check ctx eq (Eq (x, y));
      j_type x y eq

and check (ctx : context) (tm : expr) (ty : expr) : unit =
  let ty_ty = infer ctx ty in
  check_conv ctx ty_ty Type;
  let ty_tm = infer ctx tm in
  check_conv ctx ty ty_tm

and check_typable (ctx : context) (tm : expr) : unit =
  let _ = infer ctx tm in
  ()

let%test_unit "conversion-1" =
  let ctx = ("Bool", (Type, None)) :: [] in
  let u =
    of_string "Pi (n : Nat) -> Pi (x : (fun (n : Nat) -> Nat) n) -> Bool"
  in
  let t = of_string "Pi (m : Nat) -> Pi (m : Nat) -> Bool" in
  print_string "TYPE 1:  ";
  print_endline (normalize ctx u |> to_string);
  print_string "TYPE 2:  ";
  print_endline (normalize ctx t |> to_string);
  check_conv ctx u t

let%test_unit "conversion-2" =
  let ctx = [] in
  let u =
    of_string
      "Pi (n : Nat) -> Pi (x : (fun (n : Nat) -> Nat) n) -> ((fun (n : Nat)-> \
       Nat) (S n))"
  in
  let t = of_string "Pi (m : Nat) -> Pi (m : Nat) -> Nat" in
  print_string "TYPE 1:  ";
  print_endline (normalize ctx u |> to_string);
  print_string "TYPE 2:  ";
  print_endline (normalize ctx t |> to_string);
  check_conv ctx u t

let%test_unit "conversion-3" =
  let ctx = ("Bool", (Type, None)) :: [] in
  let u =
    of_string "Pi (n : Nat) -> Pi (n : (fun (n : Nat) -> Nat) n) -> Bool"
  in
  let t = of_string "Pi (m : Nat) -> Pi (m : Nat) -> Bool" in
  print_string "TYPE 1:  ";
  print_endline (normalize ctx u |> to_string);
  print_string "TYPE 2:  ";
  print_endline (normalize ctx t |> to_string);
  check_conv ctx u t

let%test_unit "infer-0" =
  let f = Abs ("x", Nat, S (Var "x")) in
  let t = Pi ("x", Nat, Nat) in
  check [] f t

let%test_unit "infer-1" =
  let ctx =
    [ ("add", (Pi ("x", Nat, Pi ("y", Nat, Nat)), None)); ("x", (Nat, None)) ]
  in
  let raw_text =
    "fun (x : Nat) -> Pi (y : Nat) -> Pi (z : Nat) -> add (add x y) z = add x \
     (add y z)"
  in
  let f = of_string raw_text in
  check ctx f (of_string "Nat => Type");

  let ctx = ("F", (Pi ("_", Nat, Type), Some f)) :: ctx in

  let raw_text = "fun (x : Nat) -> fun (IH : F x) -> IH Z" in
  let g = of_string raw_text in
  let t = infer ctx g in
  print_endline ("type of g is " ^ to_string t);
  ()

let%test_unit "infer depdent function" =
  let ctx =
    [ ("add", (Pi ("x", Nat, Pi ("y", Nat, Nat)), None)); ("x", (Nat, None)) ]
  in
  let add p q =
    let t = App (Var "add", p) in
    App (t, q)
  in
  let a0 = add (add (Var "x") (Var "y")) (Var "z") in
  let a1 = add (Var "x") (add (Var "y") (Var "z")) in
  (* fun(x : N) -> Pi(y : N) -> Pi(z : N) -> (x+y)+z = x+(y+z) *)
  let f = Abs ("x", Nat, Pi ("y", Nat, Pi ("z", Nat, Eq (a0, a1)))) in

  check ctx f (Pi ("_", Nat, Type));
  let ctx = ("F", (Pi ("_", Nat, Type), Some f)) :: ctx in
  let ctx = ("n", (Nat, None)) :: ctx in

  (* fun(r : F n) -> r Z (S Z) *)
  let g =
    Abs
      ( (* var *)
        "r",
        (* type *)
        App (Var "F", Var "n"),
        (* body *)
        App (App (Var "r", Z), S Z) )
  in
  let a0 = add (add (Var "n") Z) (S Z) in
  let a1 = add (Var "n") (add Z (S Z)) in
  let ty_g = Pi ("rr", App (Var "F", Var "n"), Eq (a0, a1)) in
  check ctx g ty_g
