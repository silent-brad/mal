open Types
open Env
open Printer
open Reader
open Ast
open Lwt.Syntax

let rec macro_expand env sexp =
  let rec qq = function
    | Pair (Symbol "unquote", Pair (e, Nil)) -> macro_expand env e
    | Pair (Symbol "unquote-splicing", _) ->
      raise (SyntaxError "splice must be inside a list")
    | Pair (a, b) when is_list (Pair (a, b)) ->
      qq_list (pair_to_list (Pair (a, b)))
    | other -> other
  and qq_list = function
    | [] -> Nil
    | Pair (Symbol "unquote-splicing", Pair (e, Nil)) :: rest ->
      (match macro_expand env e with
       | Nil -> qq_list rest
       | Pair _ as lst when is_list lst ->
         let elems = pair_to_list lst in
         List.fold_right (fun x acc -> Pair (x, acc)) elems (qq_list rest)
       | _ -> raise (SyntaxError "splice must be a list"))
    | x :: xs -> Pair (qq x, qq_list xs)
  in
  match sexp with
  | Pair (Symbol "quote", _) -> sexp
  | Pair (Symbol "quasiquote", Pair (e, Nil)) ->
    let expanded = qq e in
    macro_expand env expanded
  | Pair (Symbol "macro", _) -> sexp
  | Pair (Symbol "defmacro", _) -> sexp
  | Pair (Symbol name, args) when is_list args ->
    (try
       match lookup (name, env) with
       | Macro (ns, rest, template, menv) ->
         let arg_list = pair_to_list args in
         let expanded_template = subst ns rest arg_list template in
         let result = macro_expand menv expanded_template in
         macro_expand env result
       | _ -> Pair (Symbol name, macro_expand env args)
     with
     | NotFound _ -> Pair (Symbol name, macro_expand env args))
  | Pair (a, b) -> Pair (macro_expand env a, macro_expand env b)
  | other -> other

and subst names rest args template =
  match names, args with
  | [], [] -> template
  | n :: ns, a :: args' ->
    let template' = subst1 n a template in
    subst ns rest args' template'
  | [], args' ->
    (match rest with
     | Some r ->
       subst1
         r
         (List.fold_right (fun x acc -> Pair (x, acc)) args' Nil)
         template
     | None -> raise (TypeError "macro arity mismatch"))
  | _ -> raise (TypeError "macro arity mismatch")

and subst1 name replacement = function
  | Symbol s when s = name -> replacement
  | Pair (a, b) -> Pair (subst1 name replacement a, subst1 name replacement b)
  | Quote e -> Quote (subst1 name replacement e)
  | other -> other

let rec destructure pat value env =
  match pat with
  | PName n -> bind (n, value, env)
  | PSeq (ps, rest) ->
    if value = Nil then (
      let env' =
        List.fold_left (fun env p -> destructure p Nil env) env ps
      in
      match rest with Some r -> destructure r Nil env' | None -> env')
    else (
      let vals =
        match value with
        | Vector v -> v
        | Pair _ when is_list value -> pair_to_list value
        | _ -> raise @@ TypeError "cannot destructure non-sequence"
      in
      let rec bind_seq env ps vals =
        match ps, vals with
        | [], remaining ->
          (match rest with
           | None ->
             if remaining <> [] then
               raise @@ TypeError "too many values to destructure"
             else
               env
           | Some r ->
             let rest_list =
               List.fold_right (fun x acc -> Pair (x, acc)) remaining Nil
             in
             destructure r rest_list env)
        | p :: ps, v :: vs -> bind_seq (destructure p v env) ps vs
        | _ -> raise @@ TypeError "not enough values to destructure"
      in
      bind_seq env ps vals)
  | PMap m ->
    (match value with
     | Map map_vals ->
       let env' =
         match List.assoc_opt (Keyword "keys") m with
         | Some (PSeq (ps, _)) ->
           List.fold_left
             (fun env -> function
                | PName n ->
                  let k = Keyword n in
                  let v =
                    try List.assoc k map_vals with Not_found -> Nil
                  in
                  bind (n, v, env)
                | _ ->
                  raise @@ TypeError ":keys pattern must contain symbols")
             env
             ps
         | Some _ -> raise @@ TypeError ":keys must be followed by a vector"
         | None -> env
       in
       List.fold_left
         (fun env (k, pat) ->
            if k = Keyword "keys" then
              env
            else (
              let v = try List.assoc k map_vals with Not_found -> Nil in
              destructure pat v env))
         env'
         m
     | _ -> raise @@ TypeError "cannot destructure non-map")

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
  try ev exp with
  | e ->
    let err = Printexc.to_string e in
    print_endline @@ "Error: " ^ err ^ " in expression " ^ string_exp exp;
    raise e

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
    let stm = mkstringstream text in
    let run_sync p =
      match Lwt.state p with
      | Lwt.Return v -> v
      | Lwt.Fail e -> raise e
      | Lwt.Sleep -> Lwt_main.run p
    in
    let rec slurp env =
      try
        let sexp = run_sync (read_sexp stm) in
        let _, env' = eval_sexp sexp env in
        slurp env'
      with
      | End_of_file -> env
    in
    let new_env = slurp env in
    Symbol "ok", new_env
  | _ -> raise @@ TypeError "(load-file \"path\")"

and eval_sexp sexp env =
  let expanded = macro_expand env sexp in
  let ast = build_ast expanded in
  eval ast env

let basis =
  let numprim name op =
    ( name
    , function
      | [ Fixnum a; Fixnum b ] -> Fixnum (op a b)
      | _ -> raise @@ TypeError ("(" ^ name ^ " int int)") )
  in
  let cmpprim name op =
    ( name
    , function
      | [ Fixnum a; Fixnum b ] -> Boolean (op a b)
      | _ -> raise @@ TypeError ("(" ^ name ^ " int int)") )
  in
  let rec prim_list = function
    | [] -> Nil
    | car :: cdr -> Pair (car, prim_list cdr)
  in
  let prim_pair = function
    | [ a; b ] -> Pair (a, b)
    | _ -> raise @@ TypeError "(pair a b)"
  in
  let prim_car = function
    | [ Pair (car, _) ] -> car
    | [ Vector v ] -> if v <> [] then List.hd v else Nil
    | [ Nil ] -> Nil
    | [ e ] -> raise @@ TypeError ("(car pair) got " ^ string_val e)
    | _ -> raise @@ TypeError "(car single-arg)"
  in
  let prim_cdr = function
    | [ Pair (_, cdr) ] -> cdr
    | [ Vector v ] -> if List.length v > 1 then Vector (List.tl v) else Nil
    | [ Nil ] -> Nil
    | [ e ] -> raise @@ TypeError ("(cdr pair) got " ^ string_val e)
    | _ -> raise @@ TypeError "(cdr single-arg)"
  in
  let prim_eq = function
    | [ a; b ] -> Boolean (a = b)
    | _ -> raise @@ TypeError "(= a b)"
  in
  let prim_symp = function
    | [ Symbol _ ] -> Boolean true
    | [ _ ] -> Boolean false
    | _ -> raise @@ TypeError "(sym? single-arg)"
  in
  let prim_atomp = function
    | [ Nil ] -> Boolean true
    | [ Pair (_, _) ] -> Boolean false
    | [ _ ] -> Boolean true
    | _ -> raise @@ TypeError "(atom? single-arg)"
  in
  let prim_getchar = function
    | [] ->
      (try Fixnum (int_of_char @@ input_char stdin) with
       | End_of_file -> Fixnum (-1))
    | _ -> raise @@ TypeError "(getchar)"
  in
  let prim_print = function
    | [ v ] ->
      let () = print_string @@ string_val v in
      Symbol "ok"
    | _ -> raise @@ TypeError "(print val)"
  in
  let prim_itoc = function
    | [ Fixnum i ] -> Symbol (string_of_char @@ char_of_int i)
    | _ -> raise @@ TypeError "(itoc int)"
  in
  let prim_cat = function
    | [ Symbol a; Symbol b ] -> Symbol (a ^ b)
    | _ -> raise @@ TypeError "(cat sym syn)"
  in
  let newprim acc (name, func) = bind (name, Primitive (name, func), acc) in
  let prim_vector = function args -> Vector args in
  let prim_map = function
    | args ->
      let rec pairs = function
        | [] -> []
        | a :: b :: rest -> (a, b) :: pairs rest
        | _ -> raise @@ TypeError "(map k0 v0 k1 v1 ...)"
      in
      Map (pairs args)
  in
  let prim_seq = function
    | [ Vector v ] -> List.fold_right (fun x acc -> Pair (x, acc)) v Nil
    | [ (Pair _ as lst) ] when is_list lst -> lst
    | [ Nil ] -> Nil
    | _ -> raise @@ TypeError "(seq coll)"
  in
  let prim_get = function
    | [ Map m; key ] -> (try List.assoc key m with Not_found -> Nil)
    | [ Vector v; Fixnum i ] ->
      if i >= 0 && i < List.length v then List.nth v i else Nil
    | _ -> raise @@ TypeError "(get coll key)"
  in
  let prim_nth = function
    | [ Vector v; Fixnum i ] ->
      if i >= 0 && i < List.length v then List.nth v i else Nil
    | [ (Pair _ as lst); Fixnum i ] when is_list lst ->
      let rec nth n = function
        | [] -> Nil
        | x :: _ when n = 0 -> x
        | _ :: xs -> nth (n - 1) xs
      in
      if i >= 0 then nth i (pair_to_list lst) else Nil
    | [ Vector v; Fixnum i; default ] ->
      if i >= 0 && i < List.length v then List.nth v i else default
    | [ (Pair _ as lst); Fixnum i; default ] when is_list lst ->
      let rec nth n = function
        | [] -> default
        | x :: _ when n = 0 -> x
        | _ :: xs -> nth (n - 1) xs
      in
      if i >= 0 then nth i (pair_to_list lst) else default
    | _ -> raise @@ TypeError "(nth coll index [default])"
  in
  let prim_assoc = function
    | [ Map m; key; value ] -> Map ((key, value) :: m)
    | _ -> raise @@ TypeError "(assoc m key value)"
  in
  let gensym_counter = ref 0 in
  let prim_gensym = function
    | [] ->
      let n = !gensym_counter in
      incr gensym_counter;
      Symbol ("G_" ^ string_of_int n)
    | _ -> raise (TypeError "(gensym)")
  in
  let prim_stringp = function
    | [ String _ ] -> Boolean true
    | [ _ ] -> Boolean false
    | _ -> raise @@ TypeError "(string? val)"
  in
  let prim_vectorp = function
    | [ Vector _ ] -> Boolean true
    | [ _ ] -> Boolean false
    | _ -> raise @@ TypeError "(vector? val)"
  in
  let prim_mapp = function
    | [ Map _ ] -> Boolean true
    | [ _ ] -> Boolean false
    | _ -> raise @@ TypeError "(map? val)"
  in
  let prim_listp = function
    | [ e ] -> Boolean (is_list e)
    | _ -> raise @@ TypeError "(list? x)"
  in
  let prim_seqp = function
    | [ Nil ] | [ Pair _ ] | [ Vector _ ] -> Boolean true
    | [ _ ] -> Boolean false
    | _ -> raise @@ TypeError "(seq? x)"
  in
  let prim_numberp = function
    | [ Fixnum _ ] -> Boolean true
    | [ _ ] -> Boolean false
    | _ -> raise @@ TypeError "(number? x)"
  in
  let prim_keywordp = function
    | [ Keyword _ ] -> Boolean true
    | [ _ ] -> Boolean false
    | _ -> raise @@ TypeError "(keyword? x)"
  in
  let prim_symbolp = function
    | [ Symbol _ ] -> Boolean true
    | [ _ ] -> Boolean false
    | _ -> raise @@ TypeError "(symbol? x)"
  in
  let prim_not_eq = function
    | [ a; b ] -> Boolean (a <> b)
    | _ -> raise @@ TypeError "(not= a b)"
  in
  let prim_str = function
    | args ->
      let coerce x =
        match x with String s -> s | other -> string_val other
      in
      String (String.concat "" (List.map coerce args))
  in
  let prim_slurp = function
    | [ String s ] ->
      String (In_channel.with_open_text s In_channel.input_all)
    | _ -> raise @@ TypeError "(slurp path)"
  in
  let prim_spit = function
    | [ String path; String content ] ->
      Out_channel.with_open_text path (fun oc ->
        Out_channel.output_string oc content);
      Symbol "ok"
    | _ -> raise @@ TypeError "(spit path content)"
  in
  let prim_println = function
    | [ v ] ->
      print_endline (string_val v);
      Symbol "ok"
    | _ -> raise @@ TypeError "(println val)"
  in
  let prim_readline = function
    | [] -> (try String (read_line ()) with End_of_file -> Nil)
    | _ -> raise @@ TypeError "(read-line)"
  in
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
    ; "hash-map", prim_map
    ; "get", prim_get
    ; "assoc", prim_assoc
    ; "gensym", prim_gensym
    ; ("deref", function [ x ] -> x | _ -> raise @@ TypeError "(deref ref)")
    ; ("set", function args -> Set args)
    ; "nth", prim_nth
    ; "seq", prim_seq
    ; ( "*ns*"
      , function
        | [] -> Symbol !current_ns
        | _ -> raise @@ TypeError "(*ns*)" )
    ; ( "in-ns"
      , function
        | [ Symbol ns ] ->
          current_ns := ns;
          Symbol ns
        | _ -> raise @@ TypeError "(in-ns 'name)" )
    ]
