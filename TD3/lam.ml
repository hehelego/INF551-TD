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
let reduction t =
  let rec show_red t =
    match red t with
    | Some t' ->
        print_endline ("-> " ^ to_string t') ;
        show_red t'
    | None ->
        ()
  in
  print_endline ("   " ^ to_string t) ;
  show_red t

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
