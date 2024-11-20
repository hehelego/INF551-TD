let () = Printexc.record_backtrace true

type tvar = string
(** Type variables. *)

type var = string
(** Term variables. *)

(** Types. Either a simple type of a function type. 
    Extensions: conjunction, disjunction, truth, falsity
 *)
type ty =
  | TVar of tvar
  | Arr of ty * ty
  | Prod of ty * ty
  | Sum of ty * ty
  | Unit
  | Empty

let neg ty = Arr (ty, Empty)

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
  | CaseLR of tm * tm * tm
  | One
  | Absurd of tm * ty

type context = (var * ty) list
(** Environments. *)

let rec string_of_ty = function
  | TVar t -> t
  | Arr (dom, codom) ->
      "(" ^ string_of_ty dom ^ " => " ^ string_of_ty codom ^ ")"
  | Prod (t1, t2) -> "(" ^ string_of_ty t1 ^ " /\\ " ^ string_of_ty t2 ^ ")"
  | Sum (t1, t2) -> "(" ^ string_of_ty t1 ^ " \\/ " ^ string_of_ty t2 ^ ")"
  | Unit -> "T"
  | Empty -> "_"

let rec string_of_tm = function
  | Var x -> x
  | App (t, u) -> "(" ^ string_of_tm t ^ " " ^ string_of_tm u ^ ")"
  | Abs (x, a, t) ->
      "(fun (" ^ x ^ " : " ^ string_of_ty a ^ ") -> " ^ string_of_tm t ^ ")"
  | Pair (fst, snd) -> "(" ^ string_of_tm fst ^ ", " ^ string_of_tm snd ^ ")"
  | Fst t -> "fst(" ^ string_of_tm t ^ ")"
  | Snd t -> "snd(" ^ string_of_tm t ^ ")"
  | Left (t, _b) -> "left(" ^ string_of_tm t ^ ",)"
  | Right (_a, t) -> "right(" ^ string_of_tm t ^ ")"
  | CaseLR (disj, l, r) ->
      "case(" ^ string_of_tm disj ^ ", " ^ string_of_tm l ^ ", "
      ^ string_of_tm r ^ ")"
  | One -> "()"
  | Absurd (e, t) -> "absurd(" ^ string_of_tm e ^ ", " ^ string_of_ty t ^ ")"

exception Type_error

let rec infer_type ctx = function
  | Var x -> ( try List.assoc x ctx with Not_found -> raise Type_error)
  | App (t, u) -> (
      match infer_type ctx t with
      | Arr (dom, codom) ->
          check_type ctx u dom;
          codom
      | _ -> raise Type_error)
  | Abs (x, a, t) ->
      let b = infer_type ((x, a) :: ctx) t in
      Arr (a, b)
  | Pair (x, y) ->
      let a = infer_type ctx x in
      let b = infer_type ctx y in
      Prod (a, b)
  | Fst t -> (
      match infer_type ctx t with Prod (a, _) -> a | _ -> raise Type_error)
  | Snd t -> (
      match infer_type ctx t with Prod (_, b) -> b | _ -> raise Type_error)
  | Left (t, b) ->
      let a = infer_type ctx t in
      Sum (a, b)
  | Right (a, t) ->
      let b = infer_type ctx t in
      Sum (a, b)
  | CaseLR (t, u, v) -> (
      match infer_type ctx t with
      | Sum (a, b) -> (
          let tu = infer_type ctx u in
          let tv = infer_type ctx v in
          match (tu, tv) with
          | Arr (a', c), Arr (b', c') when a = a' && b = b' && c = c' -> c
          | _ -> raise Type_error)
      | _ -> raise Type_error)
  | One -> Unit
  | Absurd (e, a) ->
      check_type ctx e Empty;
      a

and check_type ctx tm ty =
  let _ = infer_type ctx tm = ty in
  ()

let () =
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
    check_type [ (y, b) ] (Abs (x, a, y')) (Arr (a, b));
    check_type [ (x, b); (y, b) ] (Abs (x, a, y')) (Arr (a, b));
    check_type [ (x, b); (y, a) ] (Abs (x, a, y')) (Arr (a, a));
    check_type [ (x, b); (y, a) ] (Abs (x, a, x')) (Arr (a, a))
  in
  let intro_elim =
    let x2x, x2y = (Abs (x, a, x'), Abs (x, a, y')) in
    check_type [ (x, a); (y, c); (z, a) ] (App (x2x, z')) a;
    check_type [ (x, a); (y, c); (z, b) ] (App (x2y, z')) b
  in
  (* pair / conjunction *)
  let intro_conj =
    check_type [ (x, a); (y, b) ] (Pair (x', y')) (Prod (a, b));
    check_type [ (y, b); (x, a); (z, c) ] (Pair (z', y')) (Prod (c, b))
  in
  let elim_conj =
    check_type [ (x, Prod (a, b)) ] (Fst x') a;
    check_type [ (x, Prod (a, b)) ] (Snd x') b
  in
  let comm_conj =
    let swap = Pair (Snd x', Fst (Var x)) in
    check_type [ (x, Prod (a, b)) ] swap (Prod (b, a))
  in
  (* tagged union / disjunction *)
  let intro_disj =
    check_type [ (x, a) ] (Left (x', b)) (Sum (a, b));
    check_type [ (y, b) ] (Right (a, y')) (Sum (a, b))
  in
  let elim_disj =
    let fa = Abs (x, a, z') in
    let fb = Abs (y, b, z') in
    check_type [ (x, Sum (a, b)); (z, c) ] (CaseLR (x', fa, fb)) c
  in
  let comm_disj =
    let fa = Abs (x, a, Right (b, x')) in
    let fb = Abs (y, b, Left (y', a)) in
    let swap = CaseLR (x', fa, fb) in
    check_type [ (x, Sum (a, b)) ] swap (Sum (b, a))
  in
  (* unit / truth *)
  let intro_unit = check_type [] One Unit in
  let elim_unit = check_type [ (x, Arr (Unit, a)) ] (App (x', One)) a in
  (* empty / false *)
  let ex_falso =
    check_type [ (x, Empty) ] (Absurd (x', b)) b;
    check_type [ (x, Empty) ] (Absurd (x', c)) c;
    let t = Arr (b, Arr (c, Sum (Unit, Prod (a, c)))) in
    check_type [ (x, Empty) ] (Absurd (x', t)) t
  in
  let contradict =
    check_type [ (x, a); (y, neg a) ] (Absurd (App (y', x'), c)) c;
    check_type [ (x, a); (y, neg a) ] (Absurd (App (y', x'), a)) a;
    let t = Arr (b, Arr (c, Sum (Unit, Prod (a, c)))) in
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
