open Types
open Env

let rec subst1 name replacement = function
  | Symbol s when s = name -> replacement
  | Pair (a, b) -> Pair (subst1 name replacement a, subst1 name replacement b)
  | Quote e -> Quote (subst1 name replacement e)
  | other -> other

let rec subst names rest args template =
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

let rec expand env sexp =
  let rec qq = function
    | Pair (Symbol "unquote", Pair (e, Nil)) -> expand env e
    | Pair (Symbol "unquote-splicing", _) ->
      raise (SyntaxError "splice must be inside a list")
    | Pair (a, b) when is_list (Pair (a, b)) ->
      qq_list (pair_to_list (Pair (a, b)))
    | other -> other
  and qq_list = function
    | [] -> Nil
    | Pair (Symbol "unquote-splicing", Pair (e, Nil)) :: rest ->
      (match expand env e with
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
    expand env expanded
  | Pair (Symbol "macro", _) -> sexp
  | Pair (Symbol "defmacro", _) -> sexp
  | Pair (Symbol name, args) when is_list args ->
    (try
       match lookup (name, env) with
       | Macro (ns, rest, template, menv) ->
         let arg_list = pair_to_list args in
         let expanded_template = subst ns rest arg_list template in
         let result = expand menv expanded_template in
         expand env result
       | _ -> Pair (Symbol name, expand env args)
     with
     | NotFound _ -> Pair (Symbol name, expand env args))
  | Pair (a, b) -> Pair (expand env a, expand env b)
  | other -> other
