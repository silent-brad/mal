open Types
open Env

(* Building patterns from s-expressions *)
let rec build = function
  | Symbol s -> PName s
  | Vector v -> build_seq v
  | Pair _ as p when is_list p -> build_seq (pair_to_list p)
  | Map m -> PMap (List.map (fun (k, v) -> k, build v) m)
  | _ -> raise @@ TypeError "invalid pattern"

and build_seq elems =
  let rec split acc = function
    | [] -> List.rev acc, None
    | Symbol "&" :: [ rest ] -> List.rev acc, Some (build rest)
    | Symbol "&" :: _ ->
      raise
      @@ TypeError
           "invalid pattern: & must be followed by exactly one binding"
    | x :: xs -> split (build x :: acc) xs
  in
  let fixed, rest = split [] elems in
  PSeq (fixed, rest)

let rec names = function
  | PName n -> [ n ]
  | PSeq (ps, rest) ->
    let base = List.concat (List.map names ps) in
    (match rest with None -> base | Some r -> names r @ base)
  | PMap m -> List.concat (List.map (fun (_, p) -> names p) m)

(* Destructuring: binding pattern variables to runtime values *)
let rec destructure pat value env =
  match pat with
  | PName n -> bind (n, value, env)
  | PSeq (ps, rest) -> destructure_seq ps rest value env
  | PMap m -> destructure_map m value env

and destructure_seq ps rest value env =
  if value = Nil then (
    let env' = List.fold_left (fun env p -> destructure p Nil env) env ps in
    match rest with Some r -> destructure r Nil env' | None -> env')
  else (
    let vals =
      match value with
      | Vector v -> v
      | Pair _ when is_list value -> pair_to_list value
      | _ -> raise @@ TypeError "cannot destructure non-sequence"
    in
    let rec go env ps vals =
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
      | p :: ps, v :: vs -> go (destructure p v env) ps vs
      | _ -> raise @@ TypeError "not enough values to destructure"
    in
    go env ps vals)

and destructure_map m value env =
  match value with
  | Map map_vals ->
    let env' =
      match List.assoc_opt (Keyword "keys") m with
      | Some (PSeq (ps, _)) ->
        List.fold_left
          (fun env -> function
             | PName n ->
               let k = Keyword n in
               let v = try List.assoc k map_vals with Not_found -> Nil in
               bind (n, v, env)
             | _ -> raise @@ TypeError ":keys pattern must contain symbols")
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
  | _ -> raise @@ TypeError "cannot destructure non-map"
