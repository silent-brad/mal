open Types
open Env
open Printer
open Reader
open Ast
open Macro
open Pattern
open Primitive

let error_msg e =
  match e with
  | SyntaxError msg
  | ParseError msg
  | TypeError msg
  | NotFound msg
  | UnspecifiedValue msg
  | UniqueError msg ->
    msg
  | e -> Printexc.to_string e

let print_error e =
  let file, line = !current_source in
  Printf.printf "Error at %s:%d: %s\n%!" file line (error_msg e)

let rec evalexp exp env =
  let evalapply f vs =
    match f with
    | Primitive (_, f) -> f vs
    | Closure (params, rest, e, clenv) ->
      let rec bind_args params env vals =
        match params, vals with
        | [], [] ->
          (match rest with None -> env | Some r -> destructure r Nil env)
        | [], remaining ->
          (match rest with
           | None -> raise @@ TypeError "too many arguments"
           | Some r ->
             let rest_list =
               List.fold_right (fun x acc -> Pair (x, acc)) remaining Nil
             in
             destructure r rest_list env)
        | p :: ps, v :: vs -> bind_args ps (destructure p v env) vs
        | _ -> raise @@ TypeError "arity mismatch"
      in
      let env' = bind_args params clenv vs in
      evalexp e env'
    | _ -> raise @@ TypeError "(apply prim '(args)) or (prim args)"
  in
  let rec ev = function
    | Literal (Quote e) -> e
    | Literal l -> l
    | Var n ->
      let qualified = !current_ns ^ "/" ^ n in
      (try lookup (qualified, env) with NotFound _ -> lookup (n, env))
    | If (c, t, f) when ev c = Boolean false -> ev f
    | If (c, t, f) when ev c = Nil -> ev f
    | If (c, t, f) -> ev t
    | Do [] -> Nil
    | Do [ e ] -> ev e
    | Do (e :: es) ->
      let _ = ev e in
      ev (Do es)
    | And (c1, c2) ->
      (match ev c1 with (Nil | Boolean false) as f -> f | _ -> ev c2)
    | Or (c1, c2) ->
      (match ev c1 with Nil | Boolean false -> ev c2 | other -> other)
    | Apply (fn, e) -> evalapply (ev fn) (pair_to_list (ev e))
    | Call (Var "env", []) -> env_to_val env
    | Call (e, es) -> evalapply (ev e) (List.map ev es)
    | Lambda (params, rest, e) -> Closure (params, rest, e, env)
    | Let (bs, body) ->
      let evbinding acc (pat, e) =
        let v = evalexp e acc in
        destructure pat v acc
      in
      evalexp body (List.fold_left evbinding env bs)
    | Defexp d -> raise ThisCan'tHappenError
    | LoadFile _ -> raise ThisCan'tHappenError
  in
  ev exp

let evaldef def env =
  match def with
  | Val (n, e) ->
    let qualified = !current_ns ^ "/" ^ n in
    let loc = mkloc () in
    let loc_unq = mkloc () in
    let env' = (qualified, loc) :: (n, loc_unq) :: env in
    let v = evalexp e env' in
    loc := Some v;
    loc_unq := Some v;
    v, env'
  | Exp e -> evalexp e env, env

let rec eval ast env =
  match ast with
  | Defexp d -> evaldef d env
  | LoadFile e -> eval_load_file e env
  | Do es -> eval_do es env
  | e -> evalexp e env, env

and eval_do es env =
  match es with
  | [] -> Nil, env
  | [ e ] -> eval e env
  | e :: rest ->
    let _, env' = eval e env in
    eval_do rest env'

and eval_load_file path_exp env =
  let path_val = evalexp path_exp env in
  match path_val with
  | String s ->
    let text = In_channel.with_open_text s In_channel.input_all in
    let stm = mkstringstream ~filename:s text in
    let run_sync p =
      match Lwt.state p with
      | Lwt.Return v -> v
      | Lwt.Fail e -> raise e
      | Lwt.Sleep -> Lwt_main.run p
    in
    let rec slurp env =
      try
        let sexp, source, line = run_sync (read_sexp_with_loc stm) in
        current_source := source, line;
        let _, env' = eval_sexp sexp env in
        slurp env'
      with
      | End_of_file -> env
      | e -> print_error e; env
    in
    Symbol "ok", slurp env
  | _ -> raise @@ TypeError "(load-file \"path\")"

and eval_sexp sexp env =
  let sexp_str = Printer.string_val sexp in
  try
    let expanded = Macro.expand env sexp in
    let ast = build_ast expanded in
    eval ast env
  with
  | e ->
    print_error e;
    if sexp_str <> "" then
      Printf.printf "  in: %s\n%!" sexp_str;
    Nil, env

let basis =
  List.fold_left
    newprim
    []
    [ numprim "+" ( + )
    ; numprim "-" ( - )
    ; numprim "*" ( * )
    ; numprim "/" ( / )
    ; cmpprim "<" ( < )
    ; cmpprim ">" ( > )
    ; "list", prim_list
    ; "pair", prim_pair
    ; "car", prim_car
    ; "cdr", prim_cdr
    ; "first", prim_car
    ; "rest", prim_cdr
    ; "=", prim_eq
    ; "not=", prim_not_eq
    ; "atom?", prim_atomp
    ; "sym?", prim_symp
    ; "symbol?", prim_symbolp
    ; "keyword?", prim_keywordp
    ; "number?", prim_numberp
    ; "string?", prim_stringp
    ; "vector?", prim_vectorp
    ; "map?", prim_mapp
    ; "list?", prim_listp
    ; "seq?", prim_seqp
    ; "getchar", prim_getchar
    ; "print", prim_print
    ; "println", prim_println
    ; "read-line", prim_readline
    ; "str", prim_str
    ; "slurp", prim_slurp
    ; "spit", prim_spit
    ; "itoc", prim_itoc
    ; "cat", prim_cat
    ; "vector", prim_vector
    ; "hash-map", prim_hashmap
    ; "get", prim_get
    ; "assoc", prim_assoc
    ; "gensym", prim_gensym
    ; "deref", prim_deref
    ; "set", prim_set
    ; "nth", prim_nth
    ; "seq", prim_seq
    ; "*ns*", prim_ns
    ; "in-ns", prim_in_ns
    ]
