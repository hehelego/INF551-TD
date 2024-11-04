type nat = Zero | Suc of nat

let rec nat2int = function Zero -> 0 | Suc n -> 1 + nat2int n

let%test "nat2int" =
  nat2int Zero = 0
  && nat2int (Suc Zero) = 1
  && nat2int (Suc (Suc Zero)) = 2
  && nat2int (Suc (Suc (Suc Zero))) = 3

let rec int2nat = function 0 -> Zero | n -> Suc (int2nat (n - 1))

let%test "int2nat" =
  int2nat 0 = Zero
  && int2nat 1 = Suc Zero
  && int2nat 2 = Suc (Suc Zero)
  && int2nat 3 = Suc (Suc (Suc Zero))

let rec add = function Zero -> fun m -> m | Suc n -> fun m -> Suc (add n m)

let%test "add" =
  add Zero Zero = Zero
  && add (Suc Zero) Zero = Suc Zero
  && add Zero (Suc Zero) = Suc Zero
  && add (Suc Zero) (Suc Zero) = Suc (Suc Zero)

let rec even = function
  | Zero ->
      true
  | Suc Zero ->
      false
  | Suc (Suc n) ->
      even n

let%test "even" =
  even Zero
  && even (Suc Zero) |> not
  && even (Suc (Suc Zero))
  && even (Suc (Suc (Suc Zero))) |> not

let pred = function Zero -> None | Suc n -> Some n

let%test "pred" =
  pred Zero = None
  && pred (Suc Zero) = Some Zero
  && pred (Suc (Suc Zero)) = Some (Suc Zero)
  && pred (Suc (Suc (Suc Zero))) = Some (Suc (Suc Zero))

let rec half = function Zero | Suc Zero -> Zero | Suc (Suc n) -> Suc (half n)

let%test "half" =
  half Zero = Zero
  && half (Suc Zero) = Zero
  && half (Suc (Suc Zero)) = Suc Zero
  && half (Suc (Suc (Suc Zero))) = Suc Zero
  && half (Suc (Suc (Suc (Suc Zero)))) = Suc (Suc Zero)

let rec half' = function
  | Zero ->
      Some Zero
  | Suc Zero ->
      None
  | Suc (Suc n) ->
      half' n |> Option.map (fun n -> Suc n)

let%test "half'" =
  half' Zero = Some Zero
  && half' (Suc Zero) = None
  && half' (Suc (Suc Zero)) = Some (Suc Zero)
  && half' (Suc (Suc (Suc Zero))) = None
  && half' (Suc (Suc (Suc (Suc Zero)))) = Some (Suc (Suc Zero))
