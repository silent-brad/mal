exception SyntaxError of string
exception ParseError of string
exception NotFound of string
exception TypeError of string
exception ThisCan'tHappenError
exception UnspecifiedValue of string

type 'a env = (string * 'a option ref) list

type stream =
  { mutable line_num : int
  ; mutable chr : char list
  ; chan : in_channel
  }

type lobject =
  | Fixnum of int
  | Boolean of bool
  | Symbol of string
  | Nil
  | Pair of lobject * lobject
  | Primitive of string * (lobject list -> lobject)
  | Quote of value
  | Closure of name list * exp * value env

and value = lobject
and name = string

and exp =
  | Literal of value
  | Var of name
  | If of exp * exp * exp
  | And of exp * exp
  | Or of exp * exp
  | Apply of exp * exp
  | Call of exp * exp list
  | Lambda of name list * exp
  | Defexp of def

and def =
  | Val of name * exp
  | Def of name * name list * exp
  | Exp of exp

let rec lookup = function
  | n, [] -> raise (NotFound n)
  | n, (n', v) :: _ when n = n' ->
    (match !v with Some v' -> v' | None -> raise (UnspecifiedValue n))
  | n, (n', _) :: bs -> lookup (n, bs)

(* let rec lookup (n, e) = *)
(*   match e with *)
(*   | Nil -> raise (NotFound n) *)
(*   | Pair (Pair (Symbol n', v), rst) -> if n = n' then v else lookup (n, rst) *)
(*   | _ -> raise ThisCan'tHappenError *)

(* let bind (n, v, e) = Pair (Pair (Symbol n, v), e) *)
let bind (n, v, e) = (n, ref (Some v)) :: e
let mkloc () = ref None

let bindloc ((n, vor, e) : name * 'a option ref * 'a env) : 'a env =
  (n, vor) :: e

let bindlist ns vs env =
  List.fold_left2 (fun acc n v -> bind (n, v, acc)) env ns vs

let rec env_to_val =
  let b_to_val (n, vor) =
    Pair
      (Symbol n, match !vor with None -> Symbol "unspecified" | Some v -> v)
  in
  function [] -> Nil | b :: bs -> Pair (b_to_val b, env_to_val bs)

let rec pair_to_list pr =
  match pr with
  | Nil -> []
  | Pair (a, b) -> a :: pair_to_list b
  | _ -> raise ThisCan'tHappenError

let rec is_list e =
  match e with Nil -> true | Pair (a, b) -> is_list b | _ -> false

let extend newenv oldenv =
  List.fold_right (fun (b, v) acc -> bindloc (b, v, acc)) newenv oldenv

let rec evalexp exp env =
  let evalapply f vs =
    match f with
    | Primitive (_, f) -> f vs
    | Closure (ns, e, clenv) -> evalexp e (extend (bindlist ns vs clenv) env)
    | _ -> raise (TypeError "(apply prim '(args)) or (prim args)")
  in
  let rec ev = function
    | Literal (Quote e) -> e
    | Literal l -> l
    | Var n -> lookup (n, env)
    | If (c, t, f) when ev c = Boolean true -> ev t
    | If (c, t, f) when ev c = Boolean false -> ev f
    | If _ -> raise (TypeError "(if bool e1 e2)")
    | And (c1, c2) ->
      (match ev c1, ev c2 with
       | Boolean v1, Boolean v2 -> Boolean (v1 && v2)
       | _ -> raise (TypeError "(and bool bool)"))
    | Or (c1, c2) ->
      (match ev c1, ev c2 with
       | Boolean v1, Boolean v2 -> Boolean (v1 || v2)
       | _ -> raise (TypeError "(or bool bool)"))
    | Apply (fn, e) -> evalapply (ev fn) (pair_to_list (ev e))
    | Call (Var "env", []) -> env_to_val env
    | Call (e, es) -> evalapply (ev e) (List.map ev es)
    | Lambda (ns, e) -> Closure (ns, e, env)
    | Defexp d -> raise ThisCan'tHappenError
  in
  ev exp

let evaldef def env =
  match def with
  | Val (n, e) ->
    let v = evalexp e env in
    v, bind (n, v, env)
  | Def (n, ns, e) ->
    let formals, body, cl_env =
      match evalexp (Lambda (ns, e)) env with
      | Closure (fs, bod, env) -> fs, bod, env
      | _ -> raise (TypeError "Expecting closure")
    in
    let loc = mkloc () in
    let clo = Closure (formals, body, bindloc (n, loc, cl_env)) in
    let () = loc := Some clo in
    clo, bindloc (n, loc, env)
  | Exp e -> evalexp e env, env

let rec eval ast env =
  match ast with Defexp d -> evaldef d env | e -> evalexp e env, env

let basis =
  let prim_car = function
    | [ Pair (car, _) ] -> car
    | _ -> raise (TypeError "(car non-nil-pair)")
  in
  let prim_cdr = function
    | [ Pair (_, cdr) ] -> cdr
    | _ -> raise (TypeError "(cdr non-nil-pair)")
  in
  let prim_atomp = function
    | [ Pair (_, _) ] -> Boolean false
    | [ _ ] -> Boolean true
    | _ -> raise (TypeError "(atom? something)")
  in
  let prim_eq = function
    | [ a; b ] -> Boolean (a = b)
    | _ -> raise (TypeError "(eq a b)")
  in
  let rec prim_list = function
    | [] -> Nil
    | car :: cdr -> Pair (car, prim_list cdr)
  in
  let numprim name op =
    ( name
    , function
      | [ Fixnum a; Fixnum b ] -> Fixnum (op a b)
      | _ -> raise (TypeError ("(" ^ name ^ " int int)")) )
  in
  let cmdprim name op =
    ( name
    , function
      | [ Fixnum a; Fixnum b ] -> Boolean (op a b)
      | _ -> raise (TypeError ("(" ^ name ^ " int int)")) )
  in
  let prim_pair = function
    | [ a; b ] -> Pair (a, b)
    | _ -> raise (TypeError "(pair a b)")
  in
  let newprim acc (name, func) = bind (name, Primitive (name, func), acc) in
  List.fold_left
    newprim
    []
    [ numprim "+" ( + )
    ; numprim "-" ( - )
    ; numprim "*" ( * )
    ; numprim "/" ( / )
    ; cmdprim "<" ( < )
    ; cmdprim ">" ( > )
    ; cmdprim "=" ( = )
    ; "list", prim_list
    ; "pair", prim_pair
    ; "car", prim_car
    ; "cdr", prim_cdr
    ; "eq", prim_eq
    ; "atom?", prim_atomp
    ]

let rec build_ast sexp =
  let rec cond_to_if = function
    | [] -> Literal (Symbol "error")
    | Pair (cond, Pair (res, Nil)) :: condpairs ->
      If (build_ast cond, build_ast res, cond_to_if condpairs)
    | _ -> raise (TypeError "(cond conditions)")
  in
  match sexp with
  | Primitive _ | Closure _ -> raise ThisCan'tHappenError
  | Fixnum _ | Boolean _ | Nil | Quote _ -> Literal sexp
  | Symbol s -> Var s
  | Pair _ when is_list sexp ->
    (match pair_to_list sexp with
     | [ Symbol "if"; cond; iftrue; iffalse ] ->
       If (build_ast cond, build_ast iftrue, build_ast iffalse)
     | Symbol "cond" :: conditions -> cond_to_if conditions
     | [ Symbol "and"; c1; c2 ] -> And (build_ast c1, build_ast c2)
     | [ Symbol "or"; c1; c2 ] -> Or (build_ast c1, build_ast c2)
     | [ Symbol "quote"; e ] -> Literal (Quote e)
     | [ Symbol "val"; Symbol n; e ] -> Defexp (Val (n, build_ast e))
     | [ Symbol "lambda"; ns; e ] when is_list ns ->
       let err () = raise (TypeError "(lambda (formals) body)") in
       let names =
         List.map (function Symbol s -> s | _ -> err ()) (pair_to_list ns)
       in
       Lambda (names, build_ast e)
     | [ Symbol "fn"; Symbol n; ns; e ] ->
       let err () = raise (TypeError "(fn name (formals) body)") in
       let names =
         List.map (function Symbol s -> s | _ -> err ()) (pair_to_list ns)
       in
       Defexp (Def (n, names, build_ast e))
     | [ Symbol "apply"; fnexp; args ] when is_list args ->
       Apply (build_ast fnexp, build_ast args)
     | fnexp :: args -> Call (build_ast fnexp, List.map build_ast args)
     | [] -> raise (ParseError "poorly formed expression"))
  | Pair _ -> Literal sexp
