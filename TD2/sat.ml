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

The search procedure will leverage [pick_var] to find a variable to split on.
[pick_var] will be supplied with a CNF that contains no empty clause.
 *)
let dpll_with_heuristic (pick_var : cnf -> var) =
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
            let var = pick_var cnf in
            let test value = subst_cnf var value cnf |> dpll in
            test true || test false )
  in
  dpll

let dpll_first_var =
  let pick_var cnf =
    cnf |> List.hd (* 1st clause *) |> List.hd (* 1st literal *)
    |> snd (* variable index *)
  in
  dpll_with_heuristic pick_var

let dpll = dpll_first_var

let%test_unit "dpll" =
  let x = (true, 0) in
  let x' = (false, 0) in
  let y = (true, 1) in
  let y' = (false, 1) in
  let a = [[x; y]; [x'; y]; [x'; y']] in
  let b = [[x; y]; [x'; y]; [x; y']; [x'; y']] in
  assert (dpll a) ;
  assert (not (dpll b))

(** [to_nnf] pushes negation inner by 
+ double negation elimination
+ 
*)
let rec to_nnf = function
  | Not (Not f) ->
      to_nnf f
  | Not (And (f, g)) ->
      Or (to_nnf (Not f), to_nnf (Not g))
  | Not (Or (f, g)) ->
      And (to_nnf (Not f), to_nnf (Not g))
  | And (f, g) ->
      And (to_nnf f, to_nnf g)
  | Or (f, g) ->
      Or (to_nnf f, to_nnf g)
  | True ->
      True
  | False ->
      False
  | Var v ->
      Var v
  | Not True ->
      False
  | Not False ->
      True
  | Not (Var v) ->
      Not (Var v)

(** [cnf_disj ps qs] is the disjunction of two CNFs.
    [(p1 & p2) | (q1 & q2) = (p1 | q1) & (p1 | q2) & (p2 | q1) & (p2 | q2)]
    *)
let cnf_disj ps qs = List.concat_map (fun p -> List.map (fun q -> p @ q) qs) ps

exception NotInNNF of formula

let cnf f =
  let rec transform = function
    | True ->
        []
    | False ->
        [[]]
    | Var v ->
        [[(true, v)]]
    | Not (Var v) ->
        [[(false, v)]]
    | And (f, g) ->
        transform f @ transform g
    | Or (f, g) ->
        cnf_disj (transform f) (transform g)
    | Not f ->
        raise (NotInNNF (Not f))
  in
  to_nnf f |> transform

(** [cnf_aux b f] is the CNF of
    [f] when [b = true] or [Not f] when [b = False].
*)
let rec cnf_aux b = function
  | True ->
      if b then [] else [[]]
  | False ->
      if b then [[]] else []
  | Var v ->
      [[(b, v)]]
  | Not f ->
      cnf_aux (not b) f
  | And (f, g) ->
      if b then (* f AND g = cnf(f) AND cnf(g) *)
        cnf_aux true f @ cnf_aux true g
      else
        (* NOT (f AND g) = (NOT f) OR (NOT g) *)
        cnf_disj (cnf_aux false f) (cnf_aux false g)
  | Or (f, g) ->
      if b then
        (* f OR g = cnf(f) OR cnf(g) *)
        cnf_disj (cnf_aux true f) (cnf_aux true g)
      else
        (* NOT (f OR g) = (NOT f) AND (NOT g) *)
        cnf_aux false f @ cnf_aux false g

(** [tseitin f] is a CNF g,
    such that f is SAT if and only if g is SAT.
 *)
let tseitin f =
  let rec max_var = function
    | True | False ->
        -1
    | Var v ->
        v
    | And (f, g) ->
        max (max_var f) (max_var g)
    | Or (f, g) ->
        max (max_var f) (max_var g)
    | Not f ->
        max_var f
  in
  let cnt = ref (max_var f) in
  let fresh () =
    let x = !cnt + 1 in
    cnt := x ;
    x
  in
  let clauses = ref [] in
  let append (c : clause) = clauses := c :: !clauses in
  let rec transform f =
    let z = fresh () in
    ( match f with
    | True ->
        (* z <-> True
           z
        *)
        append [(true, z)]
    | False ->
        (* z <-> False
           z'
        *)
        append [(false, z)]
    | Var x ->
        (* z <-> x
           (z -> x) AND (x -> z)
           (z' OR x) AND (x' or z)
        *)
        append [(false, z); (true, x)] ;
        append [(true, z); (false, x)]
    | Not f ->
        (* z <-> Not f
           (z -> f') AND (f' -> z)
           (z' OR f') AND (f OR z)
        *)
        let x = transform f in
        append [(true, z); (true, x)] ;
        append [(false, z); (false, x)]
    | And (f, g) ->
        (* z <-> f AND g
           (z -> f AND g) AND (f AND g -> z)
           (z -> f) AND (z -> g) AND (f' OR g' OR z)
           (z' OR f) AND (z' OR g) AND (f' OR g' OR z)
        *)
        let x = transform f in
        let y = transform g in
        append [(false, z); (true, x)] ;
        append [(false, z); (true, y)] ;
        append [(true, z); (false, x); (false, y)]
    | Or (f, g) ->
        (* z <-> f OR g
           (z -> f OR g) AND (f OR g -> z)
           (z' OR f OR g) AND ((f' AND g') OR z)
           (z' OR f OR g) AND (f' OR z) AND (g' OR z)
        *)
        let x = transform f in
        let y = transform g in
        append [(false, z); (true, x); (true, y)] ;
        append [(false, x); (true, z)] ;
        append [(false, y); (true, z)] ) ;
    z
  in
  let x = transform f in
  append [(true, x)] ;
  !clauses
