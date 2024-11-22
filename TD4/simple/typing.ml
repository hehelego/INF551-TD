open Expr

exception Type_error

let rec infer_type (ctx : context) = function
  | Var x -> ( try List.assoc x ctx with Not_found -> raise Type_error)
  | App (t, u) -> (
      match infer_type ctx t with
      | Imp (dom, codom) ->
          check_type ctx u dom;
          codom
      | _ -> raise Type_error)
  | Abs (x, a, t) ->
      let b = infer_type ((x, a) :: ctx) t in
      Imp (a, b)
  | Pair (x, y) ->
      let a = infer_type ctx x in
      let b = infer_type ctx y in
      And (a, b)
  | Fst t -> (
      match infer_type ctx t with And (a, _) -> a | _ -> raise Type_error)
  | Snd t -> (
      match infer_type ctx t with And (_, b) -> b | _ -> raise Type_error)
  | Left (t, b) ->
      let a = infer_type ctx t in
      Or (a, b)
  | Right (a, t) ->
      let b = infer_type ctx t in
      Or (a, b)
  | Case (t, x, u, y, v) -> (
      match infer_type ctx t with
      | Or (a, b) -> (
          let u = Abs (x, a, u) in
          let v = Abs (y, b, v) in
          let tu = infer_type ctx u in
          let tv = infer_type ctx v in
          match (tu, tv) with
          | Imp (a', c), Imp (b', c') when a = a' && b = b' && c = c' -> c
          | _ -> raise Type_error)
      | _ -> raise Type_error)
  | Unit -> True
  | Absurd (e, a) ->
      check_type ctx e False;
      a

and check_type ctx tm ty =
  let _ = infer_type ctx tm = ty in
  ()

let%test_unit "type inference and checking" =
  let a, b, c = (TVar "A", TVar "B", TVar "C") in
  let x, y, z = ("x", "y", "z") in
  let x', y', z' = (Var "x", Var "y", Var "z") in
  (* identity axiom *)
  let ax =
    check_type [ (x, a) ] x' a;
    check_type [ (x, a); (y, b) ] x' a;
    check_type [ (x, a); (y, b) ] y' b;
    check_type [ (y, a); (x, b); (z, c) ] x' b
  in
  (* lambda abstraction and application / implication *)
  let intro_impl =
    check_type [ (y, b) ] (Abs (x, a, y')) (Imp (a, b));
    check_type [ (x, b); (y, b) ] (Abs (x, a, y')) (Imp (a, b));
    check_type [ (x, b); (y, a) ] (Abs (x, a, y')) (Imp (a, a));
    check_type [ (x, b); (y, a) ] (Abs (x, a, x')) (Imp (a, a))
  in
  let intro_elim =
    let x2x, x2y = (Abs (x, a, x'), Abs (x, a, y')) in
    check_type [ (x, a); (y, c); (z, a) ] (App (x2x, z')) a;
    check_type [ (x, a); (y, c); (z, b) ] (App (x2y, z')) b
  in
  (* pair / conjunction *)
  let intro_conj =
    check_type [ (x, a); (y, b) ] (Pair (x', y')) (And (a, b));
    check_type [ (y, b); (x, a); (z, c) ] (Pair (z', y')) (And (c, b))
  in
  let elim_conj =
    check_type [ (x, And (a, b)) ] (Fst x') a;
    check_type [ (x, And (a, b)) ] (Snd x') b
  in
  let comm_conj =
    let swap = Pair (Snd x', Fst (Var x)) in
    check_type [ (x, And (a, b)) ] swap (And (b, a))
  in
  (* tagged union / disjunction *)
  let intro_disj =
    check_type [ (x, a) ] (Left (x', b)) (Or (a, b));
    check_type [ (y, b) ] (Right (a, y')) (Or (a, b))
  in
  let elim_disj =
    check_type [ (x, Or (a, b)); (z, c) ] (Case (x', y, z', y, z')) c;
    check_type [ (x, Or (a, b)); (z, c) ] (Case (x', x, z', x, z')) c
  in
  let comm_disj =
    let swap = Case (x', x, Right (b, x'), x, Left (x', a)) in
    check_type [ (x, Or (a, b)) ] swap (Or (b, a))
  in
  (* unit / truth *)
  let intro_unit = check_type [] Unit True in
  let elim_unit = check_type [ (x, Imp (True, a)) ] (App (x', Unit)) a in
  (* empty / false *)
  let ex_falso =
    check_type [ (x, False) ] (Absurd (x', b)) b;
    check_type [ (x, False) ] (Absurd (x', c)) c;
    let t = Imp (b, Imp (c, Or (True, And (a, c)))) in
    check_type [ (x, False) ] (Absurd (x', t)) t
  in
  let contradict =
    check_type [ (x, a); (y, neg a) ] (Absurd (App (y', x'), c)) c;
    check_type [ (x, a); (y, neg a) ] (Absurd (App (y', x'), a)) a;
    let t = Imp (b, Imp (c, Or (True, And (a, c)))) in
    check_type [ (x, a); (y, neg a) ] (Absurd (App (y', x'), t)) t
  in

  ax;
  intro_impl;
  intro_elim;
  intro_conj;
  elim_conj;
  comm_conj;
  intro_disj;
  elim_disj;
  comm_disj;
  intro_unit;
  elim_unit;
  ex_falso;
  contradict
