exception Unreachable

(** variable names *)
type var = string

(** lambda calculus terms *)
type term = Var of var | App of term * term | Abs of var * term

let rec to_string = function
  | Var x ->
      x
  | App (t, u) ->
      "(" ^ to_string t ^ " " ^ to_string u ^ ")"
  | Abs (x, t) ->
      "(\u{03bb}" ^ x ^ "." ^ to_string t ^ ")"

let%test_unit "example-lambda-terms" =
  assert (to_string (Abs ("x", App (Var "y", Var "x"))) = "(λx.(y x))") ;
  assert (to_string (App (Abs ("x", Var "y"), Var "x")) = "((λx.y) x)")

(** [has_fv x t] checks whether [x] occurs freely in term [t] *)
let rec has_fv y = function
  | Var x ->
      x = y
  | App (t, u) ->
      has_fv y t || has_fv y u
  | Abs (x, t) ->
      x <> y && has_fv y t

let%test_unit "free-variables" =
  let t = App (Var "x", Abs ("y", App (Var "y", Var "z"))) in
  assert (has_fv "x" t) ;
  assert (not (has_fv "y" t)) ;
  assert (has_fv "z" t) ;
  assert (not (has_fv "w" t))

let make_fresh label =
  let c = ref 0 in
  fun () ->
    let var = label ^ string_of_int !c in
    c := !c + 1 ;
    var

(** calls of [fresh] gives [!0, !1, !2 ...] *)
let fresh = make_fresh "!"

(** [sub x u t] gives [t[u/x]] *)
let rec sub x u = function
  | Var y ->
      if x = y then u else Var y
  | App (t1, t2) ->
      App (sub x u t1, sub x u t2)
  | Abs (y, t) ->
      if x = y then Abs (y, t)
      else if not (has_fv y u) then Abs (y, sub x u t)
      else
        let z = fresh () in
        Abs (z, t |> sub y (Var z) |> sub x u)

let%test_unit "substitutions" =
  let t = App (Var "x", Abs ("y", Var "x")) in
  let i = Abs ("x", Var "x") in
  let ti = App (Abs ("x", Var "x"), Abs ("y", Abs ("x", Var "x"))) in
  assert (sub "x" i t = ti) ;
  assert (not (sub "x" (Var "y") (Abs ("y", Var "x")) = Abs ("y", Var "y")))

(** one step beta reduction,
    we follow the call-by-name convention
 *)
let rec red = function
  | Var _ ->
      None
  | Abs (x, t) -> (
    match red t with Some t' -> Some (Abs (x, t')) | _ -> None )
  | App (Abs (x, t), u) ->
      Some (sub x u t)
  | App (t, u) -> (
    match red t with
    | Some t' ->
        Some (App (t', u))
    | None -> (
      match red u with Some u' -> Some (App (t, u')) | _ -> None ) )

(** repeatedly do beta reduction *)
let rec normalize t = match red t with Some t' -> normalize t' | None -> t

(** show reduction steps of t until a normal form *)
let reduction ?(gas = 10) t =
  let rec show_red t gas =
    match red t with
    | Some t' ->
        print_endline ("-> " ^ to_string t') ;
        if gas > 0 then show_red t' (gas - 1) else ()
    | None ->
        ()
  in
  print_endline ("   " ^ to_string t) ;
  show_red t gas

let%test_unit "normalization brute force" =
  let id = Abs ("x", Var "x") in
  let id2 = App (id, id) in
  let id3 = App (id2, id2) in
  assert (normalize id3 = id)

let%test_unit "example reduction" =
  let id = Abs ("x", Var "x") in
  let id2 = App (id, id) in
  reduction (App (id2, id2))

let eq l r = normalize l = normalize r

let%test "compare normal forms" =
  let id = Abs ("x", Var "x") in
  let id2 = App (id, id) in
  eq (App (id2, id2)) id2

(** equivalence upto alpha renaming *)
let rec alpha t u =
  match (t, u) with
  | Var x, Var y ->
      x = y
  | Abs (x, t), Abs (y, u) ->
      let z = Var (fresh ()) in
      let t' = sub x z t in
      let u' = sub y z u in
      alpha t' u'
  | App (t1, t2), App (u1, u2) ->
      alpha t1 u1 && alpha t2 u2
  | _ ->
      false

let%test_unit "alpha equivalence" =
  assert (alpha (Abs ("x", Var "x")) (Abs ("y", Var "y"))) ;
  assert (not (alpha (Abs ("x", Var "x")) (Abs ("x", Var "y"))))

let eq l r = alpha (normalize l) (normalize r)

let%test_unit "alpha-beta equivalence" =
  let t = App (Abs ("x", Abs ("y", Var "x")), Var "y") in
  print_endline (to_string (normalize t)) ;
  assert (eq t (Abs ("z", Var "y")))

let id = Abs ("x", Var "x")

let btrue = Abs ("fst", Abs ("snd", Var "fst"))

let bfalse = Abs ("fst", Abs ("snd", Var "snd"))

(** 
    [abss [x;y;z; ..] t] is [λx.λy.λz. ... t]
 *)
let abss vars term = List.fold_right (fun x t -> Abs (x, t)) vars term

let%test_unit "abss" =
  let t = Var "t" in
  assert (abss ["x"; "y"; "z"] t = Abs ("x", Abs ("y", Abs ("z", t))))

let apps = function
  | t :: ts ->
      List.fold_left (fun acc x -> App (acc, x)) t ts
  | _ ->
      raise Unreachable

let%test_unit "apps" =
  let t = Var "t" in
  let u = Var "u" in
  let v = Var "v" in
  let w = Var "w" in
  assert (apps [t; u; v; w] = App (App (App (t, u), v), w))

let bif = abss ["bool"; "fst"; "snd"] (apps [Var "bool"; Var "fst"; Var "snd"])

let%test_unit "bool-lambda-terms" =
  let t = Var "t" in
  let u = Var "u" in
  assert (eq (apps [bif; btrue; t; u]) t) ;
  assert (eq (apps [bif; bfalse; t; u]) u)

let nat n =
  let rec helper n = if n = 0 then Var "x" else App (Var "f", helper (n - 1)) in
  abss ["f"; "x"] (helper n)

let succ = abss ["n"; "f"; "x"] (App (Var "f", apps [Var "n"; Var "f"; Var "x"]))

let%test_unit "succ-lambda-term" =
  let t = apps [succ; nat 5] in
  assert (eq t (nat 6))

let add =
  abss ["n"; "m"; "f"; "x"]
    (let m = apps [Var "m"; Var "f"; Var "x"] in
     apps [Var "n"; Var "f"; m] )

let%test_unit "add-lambda-term" =
  let t = apps [add; nat 6; nat 5] in
  assert (eq t (nat 11))

let mul =
  abss ["n"; "m"; "f"; "x"]
    (let m = App (Var "m", Var "f") in
     apps [Var "n"; m; Var "x"] )

let%test_unit "mul-lambda-term" =
  let t = apps [mul; nat 0; nat 4] in
  assert (eq t (nat 0)) ;
  let t = apps [mul; nat 3; nat 0] in
  assert (eq t (nat 0)) ;
  let t = apps [mul; nat 3; nat 4] in
  assert (eq t (nat 12))

let rec eta = function
  | Abs (x, App (t, y)) when Var x = y && not (has_fv x t) ->
      Some t
  | Abs (x, t) -> (
    match eta t with Some t' -> Some (Abs (x, t')) | None -> None )
  | Var _ ->
      None
  | App (t, u) -> (
    match eta t with
    | Some t' ->
        Some (App (t', u))
    | None -> (
      match eta u with Some u' -> Some (App (t, u')) | None -> None ) )

(** TODO: study why this works *)
let rec beta_eta_normalize t =
  match red t with
  | Some t' ->
      beta_eta_normalize t'
  | None -> (
    match eta t with Some t' -> beta_eta_normalize t' | None -> t )

let eta_eq l r =
  let l', r' = (beta_eta_normalize l, beta_eta_normalize r) in
  alpha l' r'

let%test_unit "eta_eq" =
  let t =
    Abs ("x", App (Abs ("y", Abs ("z", App (Var "y", Var "z"))), Var "x"))
  in
  let u = Abs ("t", Var "t") in
  assert (eta_eq t u)

(** NOTE: dose not work for zeros *)
let exp = abss ["n"; "m"] (App (Var "m", Var "n"))

let%test_unit "exp-lambda-term" =
  let t = apps [exp; nat 1; nat 4] in
  assert (eta_eq t (nat 1)) ;
  let t = apps [exp; nat 2; nat 2] in
  assert (eta_eq t (nat 4)) ;
  let t = apps [exp; nat 3; nat 4] in
  assert (eta_eq t (nat 81))

let iszero = Abs ("n", apps [Var "n"; Abs ("x", bfalse); btrue])

let%test_unit "is-zero" =
  assert (eq (apps [iszero; nat 5]) bfalse) ;
  assert (eq (apps [iszero; nat 0]) btrue)

let pair = abss ["x"; "y"; "f"] (apps [Var "f"; Var "x"; Var "y"])

let fst = abss ["p"] (App (Var "p", btrue))

let snd = abss ["p"] (App (Var "p", bfalse))

let%test_unit "pair" =
  let t = Var "t" in
  let u = Var "u" in
  let p = apps [pair; t; u] in
  assert (eq (App (fst, p)) t) ;
  assert (eq (App (snd, p)) u)

let pred =
  abss ["n"; "f"; "x"]
    (let t = abss ["g"; "h"] (App (Var "h", App (Var "g", Var "f"))) in
     apps [Var "n"; t; Abs ("y", Var "x"); Abs ("y", Var "y")] )

let subtract = abss ["n"; "m"] (apps [Var "m"; pred; Var "n"])

let%test_unit "subs-lambda-term" =
  assert (eq (apps [subtract; nat 4; nat 5]) (nat 0)) ;
  assert (eq (apps [subtract; nat 14; nat 5]) (nat 9))

let fact_fun f n = if n = 0 then 1 else f (n - 1) * n

(** TODO: study into evaluation strategy of OCaml *)
let rec fix f n = f (fix f) n

let fact = fix fact_fun

let%test_unit "y-combinator-fact-ocaml" = assert (fact 5 = 120)

let fixpoint =
  let w = Abs ("x", App (Var "f", App (Var "x", Var "x"))) in
  Abs ("f", App (w, w))

let%test_unit "example-fixpoint-lambda-term" =
  let t = Var "t" in
  reduction (apps [fixpoint; t])

let fact_lam =
  let rec_case = apps [mul; Var "n"; App (Var "f", App (pred, Var "n"))] in
  abss ["f"; "n"] (apps [bif; App (iszero, Var "n"); nat 1; rec_case])

let fact_fun f n = if n = 0 then 1 else f (n - 1) * n

let factorial = App (fixpoint, fact_lam)

let%test_unit "factorial-lambda-term" =
  assert (eq (App (factorial, nat 0)) (nat 1)) ;
  assert (eq (App (factorial, nat 5)) (nat 120))

type dvar = int

type db = DVar of dvar | DApp of db * db | DAbs of db

(** De Bruijn representation of a closed lambda term *)
let of_term term =
  let rec trans stk = function
    | Var n -> (
      match List.find_index (( = ) n) stk with
      | Some i ->
          DVar i
      | None ->
          raise Unreachable )
    | Abs (x, t) ->
        DAbs (trans (x :: stk) t)
    | App (t, u) ->
        DApp (trans stk t, trans stk u)
  in
  trans [] term

let%test_unit "explicit-names-to-de-Bruijn" =
  let t =
    Abs
      ( "x"
      , Abs
          ( "y"
          , App
              ( App (Var "x", Abs ("z", Var "x"))
              , Abs ("x", App (Var "x", Var "y")) ) ) )
  in
  let t' =
    DAbs
      (DAbs (DApp (DApp (DVar 1, DAbs (DVar 2)), DAbs (DApp (DVar 0, DVar 1)))))
  in
  assert (of_term t = t')

let rec lift l = function
  | DVar n ->
      DVar (if n >= l then n + 1 else n)
  | DApp (t, u) ->
      DApp (lift l t, lift l u)
  | DAbs t ->
      DAbs (lift (l + 1) t)

let unlift l n =
  assert (l <> n) ;
  if l < n then n - 1 else n

let%test_unit "lift" =
  let t = lift 0 (DAbs (DApp (DVar 0, DVar 1))) in
  let t' = DAbs (DApp (DVar 0, DVar 2)) in
  assert (t = t') ;
  let t = lift 1 (DAbs (DApp (DApp (DVar 0, DVar 1), DVar 2))) in
  let t' = DAbs (DApp (DApp (DVar 0, DVar 1), DVar 3)) in
  assert (t = t')

let%test_unit "unlift" =
  assert (unlift 5 1 = 1) ;
  assert (unlift 5 4 = 4) ;
  assert (unlift 5 6 = 5) ;
  assert (unlift 5 9 = 8)

(* 1. match (level - index)
   2. capture avoiding

   /.0123(/.0123(/.0123)) (/.0123)
   reduces to
     a012(/.0b12(/.01c2))
   where
     a = /.0123
     b = /.0234
     c = /.0345
*)

(** replace occurence of v to u in term t *)
let rec dsub x u = function
  | DVar n ->
      if n = x then u
      else DVar ((* account for removal of lambda abstractions *) unlift x n)
  | DApp (t1, t2) ->
      let t1 = dsub x u t1 in
      let t2 = dsub x u t2 in
      DApp (t1, t2)
  | DAbs t ->
      let x' = x + 1 (* var x inside lambda abstraction is var (x+1) *) in
      let u' = lift 0 u (* avoid capture of free variables *) in
      DAbs (dsub x' u' t)

let rec dred = function
  | DVar _n ->
      None
  | DApp (DAbs t, u) ->
      Some (dsub 0 u t)
  | DApp (t, u) -> (
    match dred t with
    | Some t' ->
        Some (DApp (t', u))
    | None -> (
      match dred u with Some u' -> Some (DApp (t, u')) | None -> None ) )
  | DAbs t -> (
    match dred t with Some t' -> Some (DAbs t') | None -> None )

let rec dnormalize t = match dred t with Some t' -> dnormalize t' | None -> t

let%test_unit "de-bruijn-normalization" =
  let t = of_term (apps [factorial; nat 4]) in
  let u = of_term (nat 24) in
  assert (dnormalize t = dnormalize u)
