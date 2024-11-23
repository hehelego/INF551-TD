let () = Printexc.record_backtrace true

open SimpleTypes.Expr
open SimpleTypes.Parse
open SimpleTypes.Typing

(** Read the next command.

    Ignore leading or trailing white spaces.
    Ignore empty lines.
    Ignore comments that starting with a pound sign.
*)
let rec next_command () =
  let cmd = input_line stdin |> String.trim in
  let len = String.length cmd in
  if len = 0 then next_command ()
  else if String.starts_with ~prefix:"#" cmd then next_command ()
  else
    let i = String.index_opt cmd ' ' |> Option.value ~default:len in
    let c = String.sub cmd 0 i in
    let a = String.sub cmd i (len - i) |> String.trim in
    (c, a)

let any_type = TVar "*"

(** 
    Prove a proposition [goal] under a set of assumptions [env]
    by constructing a proof term [t] that inhabit the type [goal].
    That is: find [t] such that [env |- t : goal]
 *)
let rec prove env goal =
  print_endline (string_of_seq (env, goal));
  print_string "? ";
  flush_all ();
  let error e =
    print_endline e;
    prove env goal
  in
  let cmd, arg = next_command () in
  match cmd with
  | "intro" -> (
      match goal with
      | Imp (a, b) ->
          if arg = "" then error "Please provide an argument for intro."
          else
            let x = arg in
            let t = prove ((x, a) :: env) b in
            Abs (x, a, t)
      | And (a, b) ->
          let a = prove env a in
          let b = prove env b in
          Pair (a, b)
      | True -> Unit
      | _ -> error "Don't know how to introduce this.")
  | "exact" ->
      let t = tm_of_string arg in
      if infer_type env t <> goal then
        error ("Not the right type. Expecting " ^ string_of_ty goal)
      else t
  | "elim" -> (
      let term = tm_of_string arg in
      match infer_type env term with
      | Imp (premise, conclusion) when goal = conclusion ->
          let arg = prove env premise in
          App (term, arg)
      | Or (a, b) ->
          let var = arg in
          let case_left = prove ((var, a) :: env) goal in
          let case_right = prove ((var, b) :: env) goal in
          Case (term, var, case_left, var, case_right)
      | False -> Absurd (term, goal)
      | other_type ->
          error
            ("Don't know how to eliminate a term of type "
           ^ string_of_ty other_type))
  | "fst" | "snd" -> (
      let pair_term = tm_of_string arg in
      match infer_type env pair_term with
      | And (a, _b) when cmd = "fst" && a = goal -> Fst pair_term
      | And (_a, b) when cmd = "snd" && b = goal -> Snd pair_term
      | _ ->
          let exp_type =
            if cmd = "fst" then And (goal, any_type) else And (any_type, goal)
          in
          error ("Not the right type. Expecting " ^ string_of_ty exp_type))
  | "left" | "right" -> (
      match goal with
      | Or (a, b) when cmd = "left" ->
          let left = prove env a in
          Left (left, b)
      | Or (a, b) when cmd = "right" ->
          let right = prove env b in
          Right (a, right)
      | _ ->
          let exp_type = Or (any_type, any_type) in
          error ("Not the right type. Expecting " ^ string_of_ty exp_type))
  | "cut" ->
      let lemma = ty_of_string arg in
      let with_lemma = prove env (Imp (lemma, goal)) in
      let lemma_term = prove env lemma in
      App (with_lemma, lemma_term)
  | _ -> error ("Unknown command: " ^ cmd)

let () =
  print_endline "Please enter the formula to prove:";
  let goal_string = input_line stdin in
  let goal = ty_of_string goal_string in
  print_endline "Let's prove it.";
  let proof_term = prove [] goal in
  print_endline "done.";
  print_endline "Proof term is";
  print_endline (string_of_tm proof_term);
  print_string "Typechecking... ";
  flush_all ();
  assert (infer_type [] proof_term = goal);
  print_endline "ok."
