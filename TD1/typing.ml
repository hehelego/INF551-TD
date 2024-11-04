let map func = function Some x -> Some (func x) | None -> None

let bind func = function Some x -> func x | None -> None

let or_else func = function Some x -> Some x | None -> func ()

type prog =
  | Unit
  | Bool of bool
  | Int of int
  | Add of prog * prog
  | Lt of prog * prog
  | If of prog * prog * prog
  | Pair of prog * prog
  | Fst of prog
  | Snd of prog

type typ = TUnit | TBool | TInt | TProd of typ * typ

exception Type_error

let rec infer = function
  | Unit ->
      TUnit
  | Bool _ ->
      TBool
  | Int _ ->
      TInt
  | Add (p, q) -> (
    match (infer p, infer q) with TInt, TInt -> TInt | _ -> raise Type_error )
  | Lt (p, q) -> (
    match (infer p, infer q) with TInt, TInt -> TBool | _ -> raise Type_error )
  | If (p, t, f) -> (
    match infer p with
    | TBool ->
        let tt = infer t in
        let tf = infer f in
        if tt = tf then tt else raise Type_error
    | _ ->
        raise Type_error )
  | Pair (p, q) ->
      TProd (infer p, infer q)
  | Fst p -> (
    match infer p with TProd (t, _) -> t | _ -> raise Type_error )
  | Snd p -> (
    match infer p with TProd (_, t) -> t | _ -> raise Type_error )

let%test "infer" =
  infer
    (Fst
       (Pair
          ( Pair
              ( Add (Snd (Pair (Unit, Int 2)), Int 3)
              , Pair (Lt (Int 3, Add (Int 1, Int 2)), Bool true) )
          , If
              ( Lt (Int 3, Add (Int 0, Int 1))
              , If (Bool true, Bool true, Bool false)
              , Lt (Add (Add (Int 1, Int 1), Int 2), Int 10) ) ) ) )
  = TProd (TInt, TProd (TBool, TBool))

let typable p =
  try
    let _ = infer p in
    true
  with Type_error -> false

let%test_unit "typeable" =
  let prog1 = If (Lt (Add (Int 1, Int 2), Int 3), Int 4, Int 5) in
  assert (typable prog1) ;
  let prog2 = Add (Int 1, Bool false) in
  assert (typable prog2 |> not)

let rec reduce =
  let red1 p f = reduce p |> map f in
  let red2 (p, q) f =
    reduce p
    |> map (fun p' -> f (p', q))
    |> or_else (fun () -> reduce q |> map (fun q' -> f (p, q')))
  in
  function
  | Unit | Bool _ | Int _ ->
      None
  | Add (p, q) -> (
    match (p, q) with
    | Int p', Int q' ->
        Some (Int (p' + q'))
    | _ ->
        red2 (p, q) (fun (p, q) -> Add (p, q)) )
  | Lt (p, q) -> (
    match (p, q) with
    | Int p', Int q' ->
        Some (Bool (p' < q'))
    | _ ->
        red2 (p, q) (fun (p, q) -> Lt (p, q)) )
  | If (p, t, f) -> (
    match p with
    | Bool b ->
        Some (if b then t else f)
    | _ ->
        red1 p (fun p' -> If (p', t, f)) )
  | Pair (p, q) ->
      red2 (p, q) (fun (p, q) -> Pair (p, q))
  | Fst p -> (
    match p with Pair (fst, _) -> Some fst | _ -> red1 p (fun p' -> Fst p') )
  | Snd p -> (
    match p with Pair (_, snd) -> Some snd | _ -> red1 p (fun p' -> Snd p') )

let rec preduce = function
  | Unit ->
      Unit
  | Int n ->
      Int n
  | Bool b ->
      Bool b
  | Add (p, q) -> (
    match (p, q) with
    | Int p', Int q' ->
        Int (p' + q')
    | _ ->
        Add (preduce p, preduce q) )
  | Lt (p, q) -> (
    match (p, q) with
    | Int p', Int q' ->
        Bool (p' < q')
    | _ ->
        Lt (preduce p, preduce q) )
  | If (p, t, f) -> (
    match p with
    | Bool b ->
        if b then t else f |> preduce
    | _ ->
        If (preduce p, preduce t, preduce f) )
  | Pair (p, q) ->
      Pair (preduce p, preduce q)
  | Fst p -> (
    match p with Pair (fst, _) -> fst | _ -> Fst (preduce p) )
  | Snd p -> (
    match p with Pair (_, snd) -> snd | _ -> Snd (preduce p) )

let rec normalize p = match reduce p with None -> p | Some p' -> normalize p'

let rec pnormalize p =
  let p' = preduce p in
  if p = p' then p else pnormalize p'
