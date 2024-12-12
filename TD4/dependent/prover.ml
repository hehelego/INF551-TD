open NaiveDT
open Expr
open Parse_unparse
open Typing

let () = Printexc.record_backtrace true

type ansi_control = Reset | Grey | Red | Green | Yellow | Blue

let ctrl_code : ansi_control -> string = function
  | Reset -> "\027[0m"
  | Grey -> "\027[90m"
  | Red -> "\027[31m"
  | Green -> "\027[32m"
  | Yellow -> "\027[33m"
  | Blue -> "\027[34m"

let print_with_ctrl (ctrl : ansi_control) (text : string) : unit =
  let left = ctrl_code ctrl in
  let right = ctrl_code Reset in
  print_endline (left ^ text ^ right)

let split c s =
  try
    let n = String.index s c in
    ( String.trim (String.sub s 0 n),
      String.trim (String.sub s (n + 1) (String.length s - (n + 1))) )
  with Not_found -> (s, "")

let prompt_readline recording =
  print_string "? ";
  flush_all ();
  let line = input_line stdin in
  output_string recording (line ^ "\n");
  print_with_ctrl Grey ("< " ^ line);
  line

let next_command recording =
  let rec read_loop text =
    let line = prompt_readline recording |> String.trim in

    if String.starts_with ~prefix:"#" line then read_loop text
    else if String.ends_with ~suffix:";;" line then
      let n = String.length line in
      let line = String.sub line 0 (n - 2) in
      text ^ line
    else read_loop (text ^ line ^ " ")
  in
  read_loop "" |> String.trim

let () =
  (*
  env: visible bindings
  good: no error ever occurred
  loop: while loop condition
  recording: recorded inputs are written to another file
   *)
  let env = ref [] in
  let good = ref true in
  let loop = ref true in
  let recording = open_out "interactive.proof" in
  while !loop do
    try
      let cmd, arg =
        let cmd = next_command recording in
        print_with_ctrl Blue ("! " ^ cmd);
        split ' ' cmd
      in
      match cmd with
      | "assume" ->
          let x, sa = split ':' arg in
          let a = of_string sa in
          check !env a Type;
          env := (x, (a, None)) :: !env;
          print_with_ctrl Green (x ^ " assumed of type " ^ to_string a)
      | "define" ->
          let x, st = split '=' arg in
          let t = of_string st in
          let a = infer !env t in
          env := (x, (a, Some t)) :: !env;
          print_with_ctrl Green
            (x ^ " defined to " ^ to_string t ^ " of type " ^ to_string a)
      | "context" -> print_with_ctrl Green (string_of_context !env)
      | "type" ->
          let t = of_string arg in
          let a = infer !env t in
          print_with_ctrl Green (to_string t ^ " is of type " ^ to_string a)
      | "check" ->
          let t, a = split '=' arg in
          let t = of_string t in
          let a = of_string a in
          check !env t a;
          print_with_ctrl Green "Ok."
      | "eval" ->
          let t = of_string arg in
          let _ = infer !env t in
          print_with_ctrl Green (to_string (normalize !env t))
      | "exit" -> loop := false
      | "" -> ()
      | cmd -> print_with_ctrl Red ("Unknown command: " ^ cmd)
    with
    | End_of_file ->
        print_with_ctrl Red "Exit by EOF";
        good := false;
        loop := false
    | Failure err ->
        good := false;
        print_with_ctrl Yellow ("Error: " ^ err ^ ".")
    | Type_error err ->
        good := false;
        Printexc.print_backtrace stderr;
        print_with_ctrl Red ("Typing error :" ^ err ^ ".")
    | Parsing.Parse_error ->
        good := false;
        print_with_ctrl Red "Parsing error."
  done;
  if !good then print_with_ctrl Green "All good, the commands are saved"
  else
    print_with_ctrl Yellow
      "Had some problems, go fix them in the recording file";
  print_endline "Bye."
