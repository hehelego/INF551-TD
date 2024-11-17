let simple_sudoku =
  [| [|9; 9; 7; 9; 8; 2; 4; 9; 9|]
   ; [|5; 4; 9; 3; 9; 1; 9; 9; 9|]
   ; [|9; 1; 0; 9; 7; 9; 2; 9; 9|]
   ; [|2; 7; 9; 9; 5; 9; 1; 9; 8|]
   ; [|9; 6; 9; 9; 9; 9; 9; 0; 9|]
   ; [|0; 9; 8; 9; 3; 9; 9; 6; 2|]
   ; [|9; 9; 4; 9; 0; 9; 6; 2; 9|]
   ; [|9; 9; 9; 2; 9; 8; 9; 1; 5|]
   ; [|9; 9; 5; 7; 1; 9; 0; 9; 9|] |]

let medium_sudoku =
  [| [|9; 1; 9; 7; 4; 3; 9; 9; 9|]
   ; [|9; 9; 9; 5; 9; 9; 9; 9; 7|]
   ; [|9; 0; 9; 9; 9; 9; 9; 9; 8|]
   ; [|1; 9; 9; 9; 9; 9; 9; 8; 2|]
   ; [|9; 6; 4; 2; 9; 7; 5; 1; 9|]
   ; [|7; 8; 9; 9; 9; 9; 9; 9; 6|]
   ; [|3; 9; 9; 9; 9; 9; 9; 5; 9|]
   ; [|2; 9; 9; 9; 9; 1; 9; 9; 9|]
   ; [|9; 9; 9; 6; 5; 0; 9; 3; 9|] |]

let hard_sudoku =
  [| [|9; 9; 9; 9; 4; 9; 8; 9; 9|]
   ; [|8; 7; 9; 9; 9; 9; 9; 4; 9|]
   ; [|9; 3; 4; 6; 9; 9; 2; 9; 9|]
   ; [|9; 9; 3; 1; 9; 9; 7; 6; 9|]
   ; [|9; 9; 9; 0; 9; 3; 9; 9; 9|]
   ; [|9; 6; 5; 9; 9; 8; 0; 9; 9|]
   ; [|9; 9; 7; 9; 9; 0; 5; 2; 9|]
   ; [|9; 1; 9; 9; 9; 9; 9; 7; 0|]
   ; [|9; 9; 6; 9; 2; 9; 9; 9; 9|] |]

let unsolvable_sudoku =
  [| [|1; 9; 9; 8; 9; 9; 9; 9; 9|]
   ; [|9; 9; 9; 9; 9; 9; 9; 5; 9|]
   ; [|9; 9; 9; 9; 9; 0; 9; 9; 9|]
   ; [|4; 9; 1; 5; 9; 9; 3; 9; 6|]
   ; [|9; 9; 9; 9; 9; 3; 0; 9; 9|]
   ; [|9; 9; 9; 9; 8; 7; 9; 1; 2|]
   ; [|9; 9; 9; 9; 9; 2; 9; 7; 9|]
   ; [|9; 9; 4; 9; 0; 9; 9; 9; 9|]
   ; [|9; 9; 6; 9; 9; 9; 9; 9; 9|] |]

module S = Td2.Sat

(** [var i j n] asserts that [cells.(i).(j) = n] *)
let var i j n : S.var =
  let i = i mod 9 in
  let j = j mod 9 in
  (9 * ((9 * i) + j)) + n

let lit b i j n = (b, var i j n)

let map_grid f xs ys =
  List.concat_map (fun x -> List.map (fun y -> f x y) ys) xs

let x1d = [0; 1; 2; 3; 4; 5; 6; 7; 8]

let x2d =
  let pair x y = (x, y) in
  map_grid pair x1d x1d

let x3d =
  let triple (x, y) i = (x, y, i) in
  map_grid triple x2d x1d

let square_neighbors x y =
  let x, y = (x / 3 * 3, y / 3 * 3) in
  map_grid (fun i j -> (x + i, y + j)) [0; 1; 2] [0; 1; 2]

let sudoku puzzle =
  let map_neq f x xs =
    List.filter_map (fun x' -> if x <> x' then Some (f x') else None) xs
  in
  (* the solution respects the game given in argument. *)
  let conform (i, j) =
    let k = puzzle.(i).(j) in
    if k < 9 then Some [lit true i j k] else None
  in
  let part0 = List.filter_map conform x2d in
  (* there is at least one number in each cell, *)
  let cell (i, j) = List.map (lit true i j) x1d in
  let part1 = List.map cell x2d in
  (* each number occurs at most once in a row, *)
  let row (i, j, k) =
    map_neq (fun j' -> [lit false i j k; lit false i j' k]) j x1d
  in
  let part2 = List.concat_map row x3d in
  (* each number occurs at most once in a column, *)
  let col (i, j, k) =
    map_neq (fun i' -> [lit false i j k; lit false i' j k]) i x1d
  in
  let part3 = List.concat_map col x3d in
  (* each number occurs at most once in a square, *)
  let square (i, j, k) =
    let neighbors = square_neighbors i j in
    map_neq
      (fun (i', j') -> [lit false i j k; lit false i' j' k])
      (i, j) neighbors
  in
  let part4 = List.concat_map square x3d in
  (* the CNF for the sudoku puzzle *)
  let r = part0 @ part2 @ part3 @ part4 in
  assert (List.for_all (fun clause -> List.length clause <= 3) r) ;
  part0 @ part1 @ part2 @ part3 @ part4

let () = assert (S.dpll (sudoku simple_sudoku))

let () = assert (S.dpll (sudoku medium_sudoku))

let () = assert (S.dpll (sudoku hard_sudoku))

let () = assert (not (S.dpll (sudoku unsolvable_sudoku)))
