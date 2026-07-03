open Types
open Env
open Printer
open Reader

let rec evalexp exp env =
  let evalapply f vs =
    match f with
    | Primitive (_, f) -> f vs
    | Closure (ns, e, clenv) -> evalexp e (bindlist ns vs clenv)
    | _ -> raise @@ TypeError "(apply prim '(args)) or (prim args)"
  in
  let rec ev = function
    | Literal (Quote e) -> e
    | Literal l -> l
    | Var n -> lookup (n, env)
    | If (c, t, f) when ev c = Boolean true -> ev t
    | If (c, t, f) when ev c = Boolean false -> ev f
    | If (c, t, f) when ev c = Nil -> ev f
    | If _ -> raise @@ TypeError "(if bool e1 e2)"
    | Do [] -> Nil
    | Do [ e ] -> ev e
    | Do (e :: es) ->
      let _ = ev e in
      ev (Do es)
    | And (c1, c2) ->
      (match ev c1, ev c2 with
       | Boolean v1, Boolean v2 -> Boolean (v1 && v2)
       | _ -> raise @@ TypeError "(and bool bool)")
    | Or (c1, c2) ->
      (match ev c1, ev c2 with
       | Boolean v1, Boolean v2 -> Boolean (v1 || v2)
       | _ -> raise @@ TypeError "(or bool bool)")
    | Apply (fn, e) -> evalapply (ev fn) (pair_to_list (ev e))
    | Call (Var "env", []) -> env_to_val env
    | Call (e, es) -> evalapply (ev e) (List.map ev es)
    | Lambda (ns, e) -> Closure (ns, e, env)
    | Let (bs, body) ->
      let evbinding acc (n, e) = bind (n, evalexp e acc, acc) in
      evalexp body (List.fold_left evbinding env bs)
    | Defexp d -> raise ThisCan'tHappenError
  in
  try ev exp with
  | e ->
    let err = Printexc.to_string e in
    print_endline @@ "Error: " ^ err ^ " in expression " ^ string_exp exp;
    raise e

let evaldef def env =
  match def with
  | Val (n, e) ->
    let loc = mkloc () in
    let env' = (n, loc) :: env in
    let v = evalexp e env' in
    loc := Some v;
    v, env'
  | Exp e -> evalexp e env, env

let rec eval ast env =
  match ast with Defexp d -> evaldef d env | e -> evalexp e env, env

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
    | [ e ] -> raise @@ TypeError ("(car non-nil-pair) " ^ string_val e)
    | _ -> raise @@ TypeError "(car single-arg)"
  in
  let prim_cdr = function
    | [ Pair (_, cdr) ] -> cdr
    | [ e ] -> raise @@ TypeError ("(cdr non-nil-pair) " ^ string_val e)
    | _ -> raise @@ TypeError "(cdr single-arg)"
  in
  let prim_eq = function
    | [ a; b ] -> Boolean (a = b)
    | _ -> raise @@ TypeError "(eq a b)"
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
  let prim_get = function
    | [ Map m; key ] -> (try List.assoc key m with Not_found -> Nil)
    | [ Vector v; Fixnum i ] ->
      if i >= 0 && i < List.length v then List.nth v i else Nil
    | _ -> raise @@ TypeError "(get coll key)"
  in
  let prim_assoc = function
    | [ Map m; key; value ] -> Map ((key, value) :: m)
    | _ -> raise @@ TypeError "(assoc m key value)"
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
  List.fold_left
    newprim
    []
    [ numprim "+" ( + )
    ; numprim "-" ( - )
    ; numprim "*" ( * )
    ; numprim "/" ( / )
    ; cmpprim "<" ( < )
    ; cmpprim ">" ( > )
    ; cmpprim "=" ( = )
    ; "list", prim_list
    ; "pair", prim_pair
    ; "car", prim_car
    ; "cdr", prim_cdr
    ; "eq", prim_eq
    ; "atom?", prim_atomp
    ; "sym?", prim_symp
    ; "getchar", prim_getchar
    ; "print", prim_print
    ; "itoc", prim_itoc
    ; "cat", prim_cat
    ; "vector", prim_vector
    ; "map", prim_map
    ; "get", prim_get
    ; "assoc", prim_assoc
    ; "string?", prim_stringp
    ; "vector?", prim_vectorp
    ; "map?", prim_mapp
    ]
