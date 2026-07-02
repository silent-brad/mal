open Mal.Core

let rec repl stm env =
  if stm.chan = stdin then (
    print_string "> "; flush stdout);
  let ast = build_ast (read_sexp stm) in
  let result, env' = eval ast env in
  if stm.chan = stdin then
    print_endline (string_val result);
  repl stm env'

let get_ic () = try open_in Sys.argv.(1) with Invalid_argument s -> stdin

let main =
  let ic = get_ic () in
  let stm = { chr = []; line_num = 1; chan = ic } in
  try repl stm basis with End_of_file -> if ic <> stdin then close_in ic
