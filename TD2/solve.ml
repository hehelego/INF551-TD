let solver = Td2.Sat.dpll

let () =
  assert (Array.length Sys.argv = 2) ;
  let file = Sys.argv.(1) in
  let cnf = Parser.parse file in
  let msg = if solver cnf then "SAT" else "UNSAT" in
  print_endline msg
