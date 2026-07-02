open Mal.Core

let rec repl stm env =
  print_string "> ";
  flush stdout;
  let ast = build_ast (read_sexp stm) in
  let result, env' = eval ast env in
  print_endline (string_val result);
  repl stm env'

let main =
  let stm = { chr = []; line_num = 1; chan = stdin } in
  repl stm basis
