open Cljml.Core
open Lwt.Syntax

let rec repl stm env =
  let* () =
    if stm.is_stdin then (
      print_string "> "; flush stdout; Lwt.return ())
    else
      Lwt.return ()
  in
  Lwt.catch
    (fun () ->
       let* sexp, source, line = read_sexp_with_loc stm in
       Types.current_source := source, line;
       let result, env' = Eval.eval_sexp sexp env in
       let* () =
         if stm.is_stdin then (
           print_endline (string_val result);
           Lwt.return ())
         else
           Lwt.return ()
       in
       repl stm env')
    (function
      | SyntaxError msg ->
        print_endline msg;
        if stm.is_stdin then repl stm env else Lwt.return ()
      | End_of_file -> Lwt.return ()
      | e -> Lwt.fail e)

let get_input () =
  try
    let filename = Sys.argv.(1) in
    filename, open_in filename
  with
  | Invalid_argument _ -> "<stdin>", stdin

let main =
  let filename, ic = get_input () in
  Lwt_main.run (repl (mkfilestream filename ic) stdlib);
  if ic <> stdin then close_in ic
