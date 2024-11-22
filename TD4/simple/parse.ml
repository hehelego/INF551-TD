open Expr

let ty_of_string s = Parser.ty Lexer.token (Lexing.from_string s)
let tm_of_string s = Parser.tm Lexer.token (Lexing.from_string s)

let%test_unit "parsing types" =
  let l =
    [
      "A => B";
      "A ⇒ B";
      "A /\\ B";
      "A ∧ B";
      "T";
      "A \\/ B";
      "A ∨ B";
      "_";
      "not A";
      "¬ A";
    ]
  in
  List.iter
    (fun s ->
      Printf.printf "the parsing of %S is %s\n%!" s
        (string_of_ty (ty_of_string s)))
    l

let%test_unit "parsing terms" =
  let l =
    [
      "t u v";
      "fun (x : A) -> t";
      "λ (x : A) → t";
      "(t , u)";
      "fst(t)";
      "snd(t)";
      "()";
      "case t of x -> u | y -> v";
      "left(t,B)";
      "right(A,t)";
      "absurd(t,A)";
    ]
  in
  List.iter
    (fun s ->
      Printf.printf "the parsing of %S is %s\n%!" s
        (string_of_tm (tm_of_string s)))
    l

