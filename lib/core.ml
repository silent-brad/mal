exception SyntaxError of string
exception NotFound of string
exception TypeError of string
exception ThisCan'tHappenError

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

let rec lookup (n, e) =
  match e with
  | Nil -> raise (NotFound n)
  | Pair (Pair (Symbol n', v), rst) -> if n = n' then v else lookup (n, rst)
  | _ -> raise ThisCan'tHappenError

let bind (n, v, e) = Pair (Pair (Symbol n, v), e)

let rec pair_to_list pr =
  match pr with
  | Nil -> []
  | Pair (a, b) -> a :: pair_to_list b
  | _ -> raise ThisCan'tHappenError

let rec eval_sexp sexp env =
  let eval_if cond iftrue iffalse =
    let condval, _ = eval_sexp cond env in
    match condval with
    | Boolean true -> iftrue
    | Boolean false -> iffalse
    | _ -> raise (TypeError "(if bool el1 el2)")
  in
  match sexp with
  | Fixnum v -> Fixnum v, env
  | Boolean v -> Boolean v, env
  | Symbol v -> Symbol v, env
  | Nil -> Nil, env
  | Pair (Symbol "if", Pair (cond, Pair (iftrue, Pair (iffalse, Nil)))) ->
    let expval, _ = eval_sexp (eval_if cond iftrue iffalse) env in
    expval, env
  | _ -> sexp, env
