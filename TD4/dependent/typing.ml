open Expr

type typing_error =
  | MisMatch of expr * expr
  | ExpectPi of expr
  | ExpectSigma of expr
  | ExpectList of expr
  | ExpectConj of expr
  | ExpectDisj of expr
  | Unbound of var
[@@deriving show { with_path = false }]

exception Type_error of typing_error

(** [free_var x t] test whether [x] occurs freely in [t] *)
let rec free_var (x : var) : expr -> bool = function
  (* type universe *)
  | Type -> false
  (* function *)
  | Var y -> x = y
  | App (u, v) -> free_var x u || free_var x v
  (* Consider the following corner case
     Pi(x : A) . ( Pi(x : F(x)) . B(x) ) *)
  | Abs (y, t, u) | Pi (y, t, u) | Sigma (y, t, u) ->
      free_var x t || (x <> y && free_var x u)
  (* natural number *)
  | Nat | Z -> false
  | S n -> free_var x n
  | Ind (p, z, s, n) ->
      free_var x p || free_var x z || free_var x s || free_var x n
  (* equality *)
  | Eq (t, u) -> free_var x t || free_var x u
  | Refl e -> free_var x e
  | J (p, p_refl, s, t, s_eq_t) ->
      free_var x p || free_var x p_refl || free_var x s || free_var x t
      || free_var x s_eq_t
  (* coprduct *)
  | Pair (b, t, u) -> free_var x b || free_var x t || free_var x u
  | Fst t | Snd t -> free_var x t
  (* true/false and negation *)
  | True | False | Unit -> false
  | Absurd (t, a) -> free_var x t || free_var x a
  (* list *)
  | List a -> free_var x a
  | Nil a -> free_var x a
  | Cons (y, ys) -> free_var x y || free_var x ys
  | Rec (p, nil, cons, l) ->
      free_var x p || free_var x nil || free_var x cons || free_var x l
  (* logical connectives *)
  | Conj (a, b) | Disj (a, b) -> free_var x a || free_var x b
  | Proj0 p | Proj1 p -> free_var x p
  | And (a, b) | Or0 (a, b) | Or1 (a, b) -> free_var x a || free_var x b
  | Case (p, f, g) -> free_var x p || free_var x f || free_var x g

(** [subst x t u] replaces all free occurence of [x] in [u] with [t] *)
let rec subst (x : var) (tm : expr) : expr -> expr = function
  (* type universe *)
  | Type -> Type
  (* function *)
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
  (* equality types *)
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
  (* true/false and negation *)
  | True -> True
  | False -> False
  | Unit -> Unit
  | Absurd (t, a) ->
      let t' = subst x tm t in
      let a' = subst x tm a in
      Absurd (t', a')
      (* coproduct *)
  | Sigma (y, ty, u) ->
      let ty' = subst x tm ty in
      if x = y then Sigma (y, ty', u)
      else if free_var y tm then
        let z = fresh_var () in
        let u' = subst y (Var z) u in
        Sigma (z, ty', subst x tm u')
      else Sigma (y, ty', subst x tm u)
  | Pair (a, fb, b) ->
      let a' = subst x tm a in
      let fb' = subst x tm fb in
      let b' = subst x tm b in
      Pair (a', fb', b')
  | Fst pair -> Fst (subst x tm pair)
  | Snd pair -> Snd (subst x tm pair)
  (* list *)
  | List a -> List (subst x tm a)
  | Nil a -> Nil (subst x tm a)
  | Cons (y, l) ->
      let y' = subst x tm y in
      let l' = subst x tm l in
      Cons (y', l')
  | Rec (p, nil, cons, l) ->
      let p' = subst x tm p in
      let nil' = subst x tm nil in
      let cons' = subst x tm cons in
      let l' = subst x tm l in
      Ind (p', nil', cons', l')
      (* logical connectives *)
  | Conj (a, b) ->
      let a' = subst x tm a in
      let b' = subst x tm b in
      Conj (a', b')
  | And (a, b) ->
      let a' = subst x tm a in
      let b' = subst x tm b in
      And (a', b')
  | Proj0 p -> Proj0 (subst x tm p)
  | Proj1 p -> Proj1 (subst x tm p)
  | Disj (a, b) ->
      let a' = subst x tm a in
      let b' = subst x tm b in
      Disj (a', b')
  | Or0 (a, b) ->
      let a' = subst x tm a in
      let b' = subst x tm b in
      Or0 (a', b')
  | Or1 (a, b) ->
      let a' = subst x tm a in
      let b' = subst x tm b in
      Or1 (a', b')
  | Case (p, a, b) ->
      let p' = subst x tm p in
      let a' = subst x tm a in
      let b' = subst x tm b in
      Case (p', a', b')

(** test if two terms are equivalent up-to alpha-renaming *)
let rec alpha (tm : expr) (tm' : expr) : bool =
  match (tm, tm') with
  (* type universe *)
  | Type, Type -> true
  (* function *)
  | Var x, Var y -> x = y
  | App (t, u), App (t', u') -> alpha t t' && alpha u u'
  | Abs (x, t, u), Abs (y, t', u') | Pi (x, t, u), Pi (y, t', u') ->
      alpha t t'
      &&
      let z = Var (fresh_var ()) in
      let v, v' = (subst x z u, subst y z u') in
      alpha v v'
      (* natural number *)
  | Nat, Nat -> true
  | Z, Z -> true
  | S n, S n' -> alpha n n'
  | Ind (p, z, s, n), Ind (p', z', s', n') ->
      alpha p p' && alpha z z' && alpha s s' && alpha n n' (* equality *)
  | Eq (t, u), Eq (t', u') -> alpha t t' && alpha u u'
  | Refl e, Refl e' -> alpha e e'
  | J (p, r, x, y, eq), J (p', r', x', y', eq') ->
      alpha p p' && alpha r r' && alpha x x' && alpha y y' && alpha eq eq'
  (* true/false and negation *)
  | True, True -> true
  | False, False -> true
  | Unit, Unit -> true
  | Absurd (t, a), Absurd (t', a') -> alpha t t' && alpha a a'
  (* coproduct *)
  | Sigma (x, t, u), Sigma (y, t', u') ->
      alpha t t'
      &&
      let z = Var (fresh_var ()) in
      let v, v' = (subst x z u, subst y z u') in
      alpha v v'
  | Pair (a, f, b), Pair (a', f', b') -> alpha a a' && alpha f f' && alpha b b'
  | Fst p, Fst p' | Snd p, Snd p' -> alpha p p'
  (* list *)
  | List a, List a' | Nil a, Nil a' -> alpha a a'
  | Cons (x, l), Cons (x', l') -> alpha x x' && alpha l l'
  | Rec (p, nil, cons, l), Rec (p', nil', cons', l') ->
      alpha p p' && alpha nil nil' && alpha cons cons' && alpha l l' (* other *)
  (* logical connectives *)
  | Conj (a, b), Conj (a', b')
  | Disj (a, b), Disj (a', b')
  | And (a, b), And (a', b')
  | Or0 (a, b), Or0 (a', b')
  | Or1 (a, b), Or1 (a', b') ->
      alpha a a' && alpha b b'
  | Proj0 p, Proj0 p' | Proj1 p, Proj1 p' -> alpha p p'
  | Case (p, f, g), Case (p', f', g') -> alpha p p' && alpha f f' && alpha g g'
  | _ -> false

(** Reducing a term one step further if it is possible. Precondition: the input
    term is well-typed and have no free variable not in the context *)
let rec reduce (ctx : context) (e : expr) : expr option =
  let ( >> ) opt f = Option.map f opt in
  (* early return with [Some], continue alternative execution on [None] *)
  let ( let* ) opt f = match opt with Some x -> Some x | None -> f () in
  match e with
  (* type universe *)
  | Type -> None
  (* function *)
  | Var x -> (
      match List.assoc_opt x ctx with
      | Some (_ty, value) -> value
      | None -> raise (Type_error (Unbound x)))
  (* beta rule *)
  | App (Abs (x, _t, u), v) -> Some (subst x v u)
  | App (t, u) ->
      let* () = reduce ctx t >> fun t' -> App (t', u) in
      reduce ctx u >> fun u' -> App (t, u')
  (* eta rule *)
  | Abs (x, _t, App (r, Var x')) when x = x' -> Some r
  | Abs (x, t, u) ->
      let* () = reduce ctx t >> fun t' -> Abs (x, t', u) in
      let ctx' = (x, (t, None)) :: ctx in
      reduce ctx' u >> fun u' -> Abs (x, t, u')
  (* dependent function type *)
  | Pi (x, t, u) ->
      let* () = reduce ctx t >> fun t' -> Pi (x, t', u) in
      let ctx' = (x, (t, None)) :: ctx in
      reduce ctx' u >> fun u' -> Pi (x, t, u')
      (* natural number *)
  | Nat -> None
  | Z -> None
  | S n -> reduce ctx n >> fun n' -> S n'
  | Ind (_p, z, _s, Z) -> Some z
  | Ind (p, z, s, S n) ->
      let ih = Ind (p, z, s, n) in
      Some (App (App (s, n), ih))
  | Ind (p, z, s, n) ->
      let* () = reduce ctx p >> fun p' -> Ind (p', z, s, n) in
      let* () = reduce ctx z >> fun z' -> Ind (p, z', s, n) in
      let* () = reduce ctx s >> fun s' -> Ind (p, z, s', n) in
      reduce ctx n >> fun n' -> Ind (p, z, s, n')
      (* equality *)
  | Eq (t, u) ->
      let* () = reduce ctx t >> fun t' -> Eq (t', u) in
      reduce ctx u >> fun u' -> Eq (t, u')
  | Refl e -> reduce ctx e >> fun e' -> Refl e'
  | J (p, p_refl, s, t, eq) ->
      let* () = reduce ctx p >> fun p' -> J (p', p_refl, s, t, eq) in
      let* () = reduce ctx p_refl >> fun p_refl' -> J (p, p_refl', s, t, eq) in
      let* () = reduce ctx s >> fun s' -> J (p, p_refl, s', t, eq) in
      let* () = reduce ctx t >> fun t' -> J (p, p_refl, s, t', eq) in
      let* () = reduce ctx eq >> fun eq' -> J (p, p_refl, s, t, eq') in
      (* J rule: J p r x x (Refl x) => r x *)
      if alpha s t && alpha eq (Refl s) then Some (App (p_refl, s)) else None
  (* true/false and negation *)
  | True | False | Unit -> None
  | Absurd (bot, ty) ->
      let* () = reduce ctx bot >> fun bot' -> Absurd (bot', ty) in
      reduce ctx ty >> fun ty' -> Absurd (bot, ty')
  (* coproduct *)
  | Sigma (x, t, u) ->
      let* () = reduce ctx t >> fun t' -> Pi (x, t', u) in
      let ctx' = (x, (t, None)) :: ctx in
      reduce ctx' u >> fun u' -> Sigma (x, t, u')
  | Pair (a, f, b) ->
      let* () = reduce ctx a >> fun a' -> Pair (a', f, b) in
      let* () = reduce ctx f >> fun f' -> Pair (a, f', b) in
      reduce ctx b >> fun b' -> Pair (a, f, b')
  | Fst (Pair (a, _, _)) -> Some a
  | Fst p -> reduce ctx p >> fun p' -> Fst p'
  | Snd (Pair (_, _, b)) -> Some b
  | Snd p -> reduce ctx p >> fun p' -> Snd p'
  (* list *)
  | List a -> reduce ctx a >> fun a' -> List a'
  | Nil a -> reduce ctx a >> fun a' -> Nil a'
  | Cons (x, l) ->
      let* () = reduce ctx x >> fun x' -> Cons (x', l) in
      reduce ctx l >> fun l' -> Cons (x, l')
  | Rec (_p, nil, _cons, Nil _a) -> Some nil
  | Rec (p, nil, cons, Cons (x, l)) ->
      let ih = Rec (p, nil, cons, l) in
      Some (App (App (App (cons, x), l), ih))
  | Rec (p, nil, cons, l) ->
      let* () = reduce ctx p >> fun p' -> Ind (p', nil, cons, l) in
      let* () = reduce ctx nil >> fun nil' -> Ind (p, nil', cons, l) in
      let* () = reduce ctx cons >> fun cons' -> Ind (p, nil, cons', l) in
      reduce ctx l >> fun l' -> Ind (p, nil, cons, l')
  (* logical connectives *)
  | Conj (a, b) ->
      let* () = reduce ctx a >> fun a' -> Conj (a', b) in
      reduce ctx b >> fun b' -> Conj (a, b')
  | And (a, b) ->
      let* () = reduce ctx a >> fun a' -> And (a', b) in
      reduce ctx b >> fun b' -> And (a, b')
  | Proj0 (And (a, _)) -> Some a
  | Proj0 p -> reduce ctx p >> fun p' -> Proj0 p'
  | Proj1 (And (_, b)) -> Some b
  | Proj1 p -> reduce ctx p >> fun p' -> Proj1 p'
  | Disj (a, b) ->
      let* () = reduce ctx a >> fun a' -> Disj (a', b) in
      reduce ctx b >> fun b' -> Disj (a, b')
  | Or0 (a, b) ->
      let* () = reduce ctx a >> fun a' -> Or0 (a', b) in
      reduce ctx b >> fun b' -> Or0 (a, b')
  | Or1 (a, b) ->
      let* () = reduce ctx a >> fun a' -> Or1 (a', b) in
      reduce ctx b >> fun b' -> Or1 (a, b')
  | Case (Or0 (a, _), f, _) -> Some (App (f, a))
  | Case (Or1 (a, _), _, g) -> Some (App (g, a))
  | Case (p, f, g) ->
      let* () = reduce ctx p >> fun p' -> Case (p', f, g) in
      let* () = reduce ctx f >> fun f' -> Case (p, f', g) in
      reduce ctx g >> fun g' -> Case (p, f, g')

(** Normalizing a term by repeatedly reducing it NOTE: this function may not
    terminate *)
let rec normalize (ctx : context) (t : expr) : expr =
  match reduce ctx t with Some t' -> normalize ctx t' | None -> t

(** test whether two terms are alpha-beta convertible under a context *)
let conv (ctx : context) (t : expr) (t' : expr) : bool =
  let t = normalize ctx t in
  let t' = normalize ctx t' in
  alpha t t'

let check_conv (ctx : context) (t : expr) (t' : expr) : unit =
  if conv ctx t t' then () else raise (Type_error (MisMatch (t, t')))

let rec infer (ctx : context) : expr -> expr = function
  (* type universe *)
  | Type -> Type
  (* function *)
  | Var v -> (
      match List.assoc_opt v ctx with
      | Some (ty, _) -> ty
      | None -> raise (Type_error (Unbound v)))
  | App (t, u) -> (
      match infer ctx t |> normalize ctx with
      | Pi (x, arg, ret) ->
          check ctx u arg;
          subst x u ret
      | ty -> raise (Type_error (ExpectPi ty)))
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
  (* natural number *)
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
          let y, ih = (fresh_var (), fresh_var ()) in
          let p_n = App (p, Var y) in
          let p_sn = App (p, S (Var y)) in
          let ty_s_expect = Pi (y, Nat, Pi (ih, p_n, p_sn)) in
          check ctx s ty_s_expect;

          App (p, n)
      | ty -> raise (Type_error (ExpectPi ty)))
  (* equality *)
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
      (* x and y are of the same type A *)
      let a = infer ctx x in
      check ctx a Type;
      check ctx y a;
      (* p: (x y : A) -> x = y -> Type
         eq: x=y
         r: (x:A) -> p x x (Refl x) *)
      let s = fresh_var () in
      let t = fresh_var () in
      let vs, vt = (Var s, Var t) in
      let eq_pred = impl (Eq (vs, vt)) Type in
      check ctx p (Pi (s, a, Pi (t, a, eq_pred)));
      check ctx r (Pi (s, a, j_type vs vs (Refl vs)));
      check ctx eq (Eq (x, y));
      j_type x y eq
  (* true/false and negation *)
  | True | False -> Type
  | Unit -> True
  | Absurd (bot, ty) ->
      check ctx bot False;
      ty
  (* coproduct *)
  | Sigma (x, fst, snd) ->
      check ctx fst Type;
      let ctx' = (x, (fst, None)) :: ctx in
      check ctx' snd Type;
      Type
  | Pair (x, f, y) -> (
      let a = infer ctx x in
      check ctx a Type;
      let snd_type = infer ctx f |> normalize ctx in
      match snd_type with
      | Pi (z, a', _u) ->
          check_conv ctx a a';
          let b = App (f, x) in
          check ctx y b;
          Sigma (z, a, App (f, Var z))
      | ty -> raise (Type_error (ExpectPi ty)))
  | Fst p -> (
      match infer ctx p |> normalize ctx with
      | Sigma (_x, a, _b) -> a
      | ty -> raise (Type_error (ExpectSigma ty)))
  | Snd p -> (
      match infer ctx p |> normalize ctx with
      | Sigma (x, a, b) -> App (Abs (x, a, b), Fst p)
      | ty -> raise (Type_error (ExpectSigma ty)))
  (* list *)
  | List a ->
      check ctx a Type;
      Type
  | Nil a ->
      check ctx a Type;
      List a
  | Cons (x, l) ->
      let a = infer ctx x in
      check ctx a Type;
      check ctx l (List a);
      List a
  | Rec (p, nil, cons, ls) -> (
      (*
      p : List A -> Type
      nil : p []
      cons : (x : A) (l : List A) (ih : p l) -> p (x :: l)
      ls : List A
      *)
      match infer ctx ls |> normalize ctx with
      | List a ->
          check ctx p (impl (List a) Type);
          check ctx nil (App (p, Nil a));
          let x, l, ih = (fresh_var (), fresh_var (), fresh_var ()) in
          let type_cons =
            Pi
              ( x,
                a,
                Pi
                  ( l,
                    List a,
                    Pi (ih, App (p, Var l), App (p, Cons (Var x, Var l))) ) )
          in
          check ctx cons type_cons;
          App (p, ls)
      | ty -> raise (Type_error (ExpectList ty)))
  (* logical connectives *)
  | Conj (a, b) | Disj (a, b) ->
      check ctx a Type;
      check ctx b Type;
      Type
  | And (a, b) ->
      let ta = infer ctx a in
      let tb = infer ctx b in
      check ctx ta Type;
      check ctx tb Type;
      Conj (ta, tb)
  | Proj0 p -> (
      match infer ctx p |> normalize ctx with
      | Conj (a, _) -> a
      | ty -> raise (Type_error (ExpectConj ty)))
  | Proj1 p -> (
      match infer ctx p |> normalize ctx with
      | Conj (_, b) -> b
      | ty -> raise (Type_error (ExpectConj ty)))
  | Or0 (x, b) ->
      let a = infer ctx x in
      check ctx a Type;
      check ctx b Type;
      Disj (a, b)
  | Or1 (y, a) ->
      let b = infer ctx y in
      check ctx b Type;
      check ctx a Type;
      Disj (a, b)
  | Case (p, f, g) -> (
      match infer ctx p |> normalize ctx with
      | Disj (a, b) -> (
          let tf = infer ctx f |> normalize ctx in
          match tf with
          | Pi (_, _, c) ->
              check_conv ctx tf (impl a c);
              check ctx g (impl b c);
              c
          | ty -> raise (Type_error (ExpectPi ty)))
      | ty -> raise (Type_error (ExpectDisj ty)))

(** [check ctx tm ty] validate that under context [ctx] term [tm] has type [ty]
*)
and check (ctx : context) (tm : expr) (ty : expr) : unit =
  let ty_ty = infer ctx ty in
  check_conv ctx ty_ty Type;
  let ty_tm = infer ctx tm in
  check_conv ctx ty_tm ty

and check_typable (ctx : context) (tm : expr) : unit =
  let _ = infer ctx tm in
  ()

(*
let%test_unit "reduce_0" =
  let ctx = [ ("Bool", (Type, None)) ] in
  let u =
    Pi
      ( "Bool",
        Type,
        Pi ("n", Nat, Pi ("x", App (Abs ("n", Nat, Nat), Var "n"), Var "Bool"))
      )
  in
  let u' = Pi ("Bool", Type, Pi ("n", Nat, Pi ("x", Nat, Var "Bool"))) in
  assert (normalize ctx u = u')

let%test_unit "conversion-1" =
  let ctx = [ ("Bool", (Type, None)) ] in
  let u =
    of_string "Pi (n : Nat) -> Pi (x : (fun (n : Nat) -> Nat) n) -> Bool"
  in
  let t = of_string "Pi (m : Nat) -> Pi (m : Nat) -> Bool" in
  check_conv ctx u t

let%test_unit "conversion-2" =
  let u =
    [
      "Pi (n : Nat) ->";
      "Pi (x : (fun (n : Nat) -> Nat) n) ->";
      "(fun (n : Nat) -> Nat) (S n)";
    ]
    |> String.concat " " |> of_string
  in
  let t = of_string "Pi (m : Nat) -> Pi (m : Nat) -> Nat" in
  check_conv [] u t

let%test_unit "conversion-3" =
  let ctx = [ ("Bool", (Type, None)) ] in
  let u =
    of_string "Pi (n : Nat) -> Pi (n : (fun (n : Nat) -> Nat) n) -> Bool"
  in
  let t = of_string "Pi (m : Nat) -> Pi (m : Nat) -> Bool" in
  check_conv ctx u t

let%test_unit "infer-0" =
  let f = Abs ("x", Nat, S (Var "x")) in
  let t = Pi ("x", Nat, Nat) in
  check [] f t

let%test_unit "infer-1" =
  let f =
    [
      "fun (x : Nat) ->";
      "Pi (y : Nat) ->";
      "Pi (z : Nat) ->";
      "add (add x y) z = add x (add y z)";
    ]
    |> String.concat " " |> of_string
  in
  let g = of_string "fun (x : Nat) -> fun (IH : F x) -> IH Z" in
  let ty_g =
    [
      "Pi (x : Nat) ->";
      "Pi (IH : (F x)) ->";
      "Pi (z : Nat) ->";
      "add (add x Z) z = add x (add Z z)";
    ]
    |> String.concat " " |> of_string
  in
  let ctx =
    [
      ("add", (Pi ("x", Nat, Pi ("y", Nat, Nat)), None));
      ("x", (Nat, None));
      ("F", (impl Nat Type, Some f));
    ]
  in
  check ctx f (impl Nat Type);
  check ctx g ty_g

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

let%test_unit "normalize" =
  let ctx =
    [
      ("suc", (Pi ("_", Nat, Nat), Some (Abs ("k", Nat, S (Var "k")))));
      ("x", (Nat, None));
    ]
  in
  let tm =
    Pi
      ( "y",
        Nat,
        Pi
          ( "IH",
            Eq
              ( Ind
                  ( Abs ("n", Nat, Nat),
                    Var "y",
                    Abs ("m", Nat, Abs ("s", Nat, S (Var "s"))),
                    Var "x" ),
                Ind
                  ( Abs ("n", Nat, Nat),
                    Var "x",
                    Abs ("m", Nat, Abs ("s", Nat, S (Var "s"))),
                    Var "y" ) ),
            Eq
              ( Ind
                  ( Abs ("n", Nat, Nat),
                    S (Var "y"),
                    Abs ("m", Nat, Abs ("s", Nat, S (Var "s"))),
                    Var "x" ),
                S
                  (Ind
                     ( Abs ("n", Nat, Nat),
                       Var "x",
                       Abs ("m", Nat, Abs ("s", Nat, S (Var "s"))),
                       Var "y" )) ) ) )
  in
  let tm' =
    Pi
      ( "y",
        Nat,
        Pi
          ( "IH",
            Eq
              ( Ind
                  ( Abs ("n", Nat, Nat),
                    Var "y",
                    Abs ("m", Nat, Abs ("s", Nat, S (Var "s"))),
                    Var "x" ),
                Ind
                  ( Abs ("n", Nat, Nat),
                    Var "x",
                    Abs ("m", Nat, Abs ("s", Nat, S (Var "s"))),
                    Var "y" ) ),
            Eq
              ( Ind
                  ( Abs ("n", Nat, Nat),
                    App (Var "suc", Var "y"),
                    Abs ("m", Nat, Abs ("s", Nat, S (Var "s"))),
                    Var "x" ),
                S
                  (Ind
                     ( Abs ("n", Nat, Nat),
                       Var "x",
                       Abs ("m", Nat, Abs ("s", Nat, S (Var "s"))),
                       Var "y" )) ) ) )
  in
  assert (normalize ctx tm' <> tm');
  check_conv ctx tm tm'

let%test_unit "check-conj" =
  let x, x' = ("x", Var "x") in
  let ctx = [ (x, (Nat, None)) ] in
  let t = Pair (Nat, Pair (x', Refl x')) in
  check ctx t (Conj (Type, Conj (Nat, Eq (x', x'))));
  check ctx (Conj (Type, Nat)) Type;
  check ctx (Proj0 t) Type;
  check ctx (Proj0 (Proj1 t)) Nat

let%test_unit "reduce-conj" =
  let pair = Pair (Z, S Z) in
  check_conv [] (Proj0 pair) Z;
  check_conv [] (Proj1 pair) (S Z);
  ()

let%test_unit "check-disj" =
  let f, g, t = (Var "f", Var "g", Var "T") in
  let ctx =
    [
      ("T", (Type, None));
      ("f", (Pi ("_", Nat, Var "T"), None));
      ("g", (Pi ("_", True, Var "T"), None));
    ]
  in
  let t0 = Left (Z, True) in
  let t1 = Right (Nat, Unit) in
  check ctx t0 (Disj (Nat, True));
  check ctx t1 (Disj (Nat, True));
  let u0 = Case (t0, f, g) in
  let u1 = Case (t0, f, g) in
  check ctx u0 t;
  check ctx u1 t

  *)
