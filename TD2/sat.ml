type var = int

type formula =
  | True
  | False
  | Var of var
  | Not of formula
  | And of formula * formula
  | Or of formula * formula

(** [subst x f g] is the formula yielded by replacing all occurrences of variable x with another formula g
    *)
let subst x f =
  let rec sub = function
    | Var y when x = y ->
        f
    | Not g ->
        Not (sub g)
    | And (g, h) ->
        And (sub g, sub h)
    | Or (g, h) ->
        Or (sub g, sub h)
    | g ->
        (* True | False | Var y when y <> x*)
        g
  in
  sub

(** find a variable in the formula *)
let rec free_var = function
  | True | False ->
      None
  | Var v ->
      Some v
  | Not f ->
      free_var f
  | And (f, g) -> (
    match free_var f with Some x -> Some x | None -> free_var g )
  | Or (f, g) -> (
    match free_var f with Some x -> Some x | None -> free_var g )

(** [UnassignedVariable x] is raised when one attempts to evaluate a formula that contains a free occurrence of x *)
exception UnassignedVariable of var

(** evaluate the truth value of a formula which contains no free variable *)
let rec eval = function
  | True ->
      true
  | False ->
      false
  | Var v ->
      raise (UnassignedVariable v)
  | Not f ->
      not (eval f)
  | And (f, g) ->
      eval f && eval g
  | Or (f, g) ->
      eval f || eval g

(** naive DFS search for satisfying assignment *)
let rec sat_simple f =
  match free_var f with
  | Some x ->
      let test v = subst x v f |> sat_simple in
      test True || test False
  | None ->
      eval f

let%test_unit "sat-simple" =
  let x = Var 0 in
  let x' = Not x in
  let y = Var 1 in
  let y' = Not y in
  let a = And (And (Or (x, y), Or (x', y)), Or (x', y')) in
  let b = And (And (Or (x, y), Or (x', y)), And (Or (x, y'), Or (x', y'))) in
  assert (sat_simple a) ;
  assert (not (sat_simple b))

(** [(polarity, varialbe)] a literal is either a variable or the negation of a variable *)
type literal = bool * var

(** [clause] a disjunctive clause is the disjunction of zero, one, or more literals,
    represented by a list of [literal]s
 *)
type clause = literal list

(** [cnf] a conjunctive normal form is the conjunction of zero, one, or more disjunctive clauses,
    represented by a list of [clause]s
 *)
type cnf = clause list

(** [subst_cnf x v cnf]
    is the CNF yielded by the truth value of variable [x] to [v] in [cnf]
 *)
let subst_cnf x v cnf =
  let not_mem x xs = not (List.mem x xs) in
  match v with
  | true ->
      cnf
      (* clauses where x positively occur are satisfied *)
      |> List.filter (not_mem (true, x))
      (* negative occurances of x evaluate to false *)
      |> List.map (List.filter (( <> ) (false, x)))
  | false ->
      cnf
      |> List.filter (not_mem (false, x))
      |> List.map (List.filter (( <> ) (true, x)))

(** naive DFS search for satisfying assignment with a pruning strategy
    that stop whenever the partial assignment already determines the value of the whole CNF
 *)
let rec dpll_simple = function
  | [] ->
      (* no more clauses to satisfy *)
      true
  | cnf when List.mem [] cnf ->
      (* one clause is unsatisfiable *)
      false
  | cnf ->
      (* precondition: every disjunctive clause is non-empty *)
      let _polar, var =
        cnf |> List.hd (* 1st clause *) |> List.hd (* 1st literal *)
      in
      let test value = subst_cnf var value cnf |> dpll_simple in
      test true || test false

let%test_unit "dpll-simple" =
  let x = (true, 0) in
  let x' = (false, 0) in
  let y = (true, 1) in
  let y' = (false, 1) in
  let a = [[x; y]; [x'; y]; [x'; y']] in
  let b = [[x; y]; [x'; y]; [x; y']; [x'; y']] in
  assert (dpll_simple a) ;
  assert (not (dpll_simple b))

(** a unit clause is a clause with exactly one unassigned literal *)
let rec find_unitary = function
  | [] ->
      None
  | [lit] :: _ ->
      Some lit
  | _ :: cs ->
      find_unitary cs

let%test_unit "unitary-clause" =
  let x = (true, 0) in
  let y = (true, 1) in
  let y' = (false, 1) in
  assert (find_unitary [[x; y]; [x]; [y; y']] = Some x) ;
  assert (find_unitary [[x; y]; [y; y']] = None)

(** Find the first element that

+ either occurs in xs but not in ys
+ or occurs in ys but not in xs
*)
let head_xor xs ys =
  let not_in xs x = not (List.mem x xs) in
  match List.find_opt (not_in ys) xs with
  | Some x ->
      Some (true, x)
  | None -> (
    match List.find_opt (not_in xs) ys with
    | Some y ->
        Some (false, y)
    | None ->
        None )

let%test_unit "head_xor" =
  assert (head_xor [] [] = None) ;
  assert (head_xor [1] [] = Some (true, 1)) ;
  assert (head_xor [] [2] = Some (false, 2)) ;
  assert (head_xor [1] [1; 2] = Some (false, 2)) ;
  assert (head_xor [1; 2] [1] = Some (true, 2)) ;
  assert (head_xor [1; 2] [1; 2] = None) ;
  assert (head_xor [1; 2; 3] [1; 2] = Some (true, 3))

(** A pure literal (polarity, variable) must

+ (polarity, variable) occurs
+ (not polarity, variable) never occurs
*)
let find_pure cnf =
  let split_polar = function
    | true, var ->
        Either.Left var
    | false, var ->
        Either.Right var
  in
  let pos, neg = cnf |> List.flatten |> List.partition_map split_polar in
  let sort_uniq = List.sort_uniq compare in
  head_xor (sort_uniq pos) (sort_uniq neg)

let%test_unit "pure-literal" =
  let x = (true, 0) in
  let x' = (false, 0) in
  let y = (true, 1) in
  let y' = (false, 1) in
  assert (find_pure [[x; y]; [x]; [x'; y]] = Some y) ;
  assert (find_pure [[x; y']; [x]; [x'; y']] = Some y') ;
  assert (find_pure [[x; y']; [x]; [x'; y]] = None)

(** DPLL SAT solving:

+ unit propagation
+ pure elimination
 *)
let rec dpll cnf =
  if cnf = [] then (* no more clauses to satisfy *)
    true
  else if List.mem [] cnf then (* one clause is unsatisfiable *)
    false
  else
    match find_unitary cnf with
    | Some (v, x) ->
        (* the value of [x] must be [v] *)
        cnf |> subst_cnf x v |> dpll
    | None -> (
      match find_pure cnf with
      | Some (v, x) ->
          (* safe to set [x] to [v] *)
          cnf |> subst_cnf x v |> dpll
      | None ->
          (* precondition: every disjunctive clause is non-empty *)
          let _polar, var =
            cnf |> List.hd (* 1st clause *) |> List.hd (* 1st literal *)
          in
          let test value = subst_cnf var value cnf |> dpll in
          test true || test false )

let%test_unit "dpll" =
  let x = (true, 0) in
  let x' = (false, 0) in
  let y = (true, 1) in
  let y' = (false, 1) in
  let a = [[x; y]; [x'; y]; [x'; y']] in
  let b = [[x; y]; [x'; y]; [x; y']; [x'; y']] in
  assert (dpll a) ;
  assert (not (dpll b))
