(* Taken from https://www.lix.polytechnique.fr/Labo/Samuel.Mimram/teaching/INF551/TD/2.sat.html#the-dpll-algorithm
   Create by Samuel Mimram and Stéphane Lengrand
*)

let parse f =
  let load_file f =
    let ic = open_in f in
    let n = in_channel_length ic in
    let s = Bytes.create n in
    really_input ic s 0 n ; close_in ic ; Bytes.to_string s
  in
  let f = load_file f in
  let f = String.map (function '\t' -> ' ' | c -> c) f in
  let f = String.split_on_char '\n' f in
  let f = List.map (String.split_on_char ' ') f in
  let f = List.filter (function "c" :: _ | "p" :: _ -> false | _ -> true) f in
  let f = List.flatten f in
  let aux (a, c) = function
    | "" ->
        (a, c)
    | "0" ->
        (c :: a, [])
    | n ->
        let n = int_of_string n in
        let x = if n < 0 then (false, -n) else (true, n) in
        (a, x :: c)
  in
  fst (List.fold_left aux ([], []) f)
