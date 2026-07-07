open Types
open Env

let rec assert_unique = function
  | [] -> ()
  | x :: xs ->
    if List.mem x xs then raise @@ UniqueError x else assert_unique xs

let rec build_pattern = function
  | Symbol s -> PName s
  | Vector v -> build_seq_pattern v
  | Pair _ as p when is_list p ->
    let v = pair_to_list p in
    build_seq_pattern v
  | Map m -> PMap (List.map (fun (k, v) -> k, build_pattern v) m)
  | _ -> raise @@ TypeError "invalid pattern"

and build_seq_pattern elems =
  let rec split acc = function
    | [] -> List.rev acc, None
    | Symbol "&" :: [ rest ] -> List.rev acc, Some (build_pattern rest)
    | Symbol "&" :: _ ->
      raise
      @@ TypeError
           "invalid pattern: & must be followed by exactly one binding"
    | x :: xs -> split (build_pattern x :: acc) xs
  in
  let fixed, rest = split [] elems in
  PSeq (fixed, rest)

let rec pattern_names = function
  | PName n -> [ n ]
  | PSeq (ps, rest) ->
    let names = List.concat (List.map pattern_names ps) in
    (match rest with None -> names | Some r -> pattern_names r @ names)
  | PMap m -> List.concat (List.map (fun (_, p) -> pattern_names p) m)

let rec build_ast sexp =
  let rec quasiquote = function
    | Pair (Symbol "unquote", Pair (e, Nil)) -> e
    | Pair (Symbol "unquote-splicing", _) ->
      raise (SyntaxError "splice must be inside a list")
    | Pair (a, b) when is_list (Pair (a, b)) ->
      let elems = pair_to_list (Pair (a, b)) in
      qq_list elems
    | other ->
      (* Atom: produce (quote other) *)
      Pair (Symbol "quote", Pair (other, Nil))
  and qq_list = function
    | [] -> Nil
    | Pair (Symbol "unquote-splicing", Pair (e, Nil)) :: rest ->
      (* splice: produce (append e rest-result) *)
      Pair (Symbol "append", Pair (e, Pair (qq_list rest, Nil)))
    | x :: xs ->
      let car = quasiquote x in
      let cdr = qq_list xs in
      Pair (Symbol "pair", Pair (car, Pair (cdr, Nil)))
  in
  let rec cond_to_if = function
    | [] -> Literal (Symbol "error")
    | Pair (cond, Pair (res, Nil)) :: condpairs ->
      If (build_ast cond, build_ast res, cond_to_if condpairs)
    | _ -> raise @@ TypeError "(cond c0 c1 c2 c3 ...)"
  in
  let parse_params raw err =
    let rec split = function
      | [] -> [], None
      | "&" :: [ rest ] -> [], Some rest
      | "&" :: _ -> err ()
      | x :: xs ->
        let args, r = split xs in
        x :: args, r
    in
    split raw
  in
  match sexp with
  | Primitive _ | Closure _ | Macro _ -> raise ThisCan'tHappenError
  | Fixnum _ | Boolean _ | Nil | Quote _ | String _ | Vector _ | Map _
  | Set _ | Keyword _ ->
    Literal sexp
  | Symbol s -> Var s
  | Pair _ when is_list sexp ->
    (match pair_to_list sexp with
     | Symbol "if" :: [ cond; iftrue ] ->
       If (build_ast cond, build_ast iftrue, Literal Nil)
     | Symbol "if" :: [ cond; iftrue; iffalse ] ->
       If (build_ast cond, build_ast iftrue, build_ast iffalse)
     | Symbol "cond" :: conditions -> cond_to_if conditions
     | [ Symbol "and"; c1; c2 ] -> And (build_ast c1, build_ast c2)
     | [ Symbol "or"; c1; c2 ] -> Or (build_ast c1, build_ast c2)
     | [ Symbol "quote"; e ] -> Literal (Quote e)
     | [ Symbol "quasiquote"; e ] -> build_ast (Quote (quasiquote e))
     | [ Symbol "def"; Symbol n; e ] -> Defexp (Val (n, build_ast e))
     | Symbol "let" :: bindings :: body when body <> [] ->
       let mkbinding = function
         | Pair (pat, Pair (e, Nil)) -> build_pattern pat, build_ast e
         | _ -> raise @@ TypeError "(let bindings ...body)"
       in
       let mkbinding_vec bs =
         let rec pairup = function
           | [] -> []
           | pat :: e :: rest ->
             (build_pattern pat, build_ast e) :: pairup rest
           | _ -> raise @@ TypeError "(let [pattern val ...] body)"
         in
         pairup bs
       in
       let bindings =
         match bindings with
         | Vector v -> mkbinding_vec v
         | _ when is_list bindings ->
           List.map mkbinding (pair_to_list bindings)
         | _ -> raise @@ TypeError "(let bindings ...body)"
       in
       let all_names =
         List.concat (List.map (fun (pat, _) -> pattern_names pat) bindings)
       in
       let () = assert_unique all_names in
       let body_ast =
         match body with
         | [ e ] -> build_ast e
         | es -> Do (List.map build_ast es)
       in
       Let (bindings, body_ast)
     | [ Symbol "fn"; ns; e ] ->
       let err () = raise @@ TypeError "(fn [formals] body)" in
       let raw =
         match ns with
         | Vector v -> v
         | Symbol s -> [ Symbol s ]
         | _ when is_list ns -> pair_to_list ns
         | _ -> err ()
       in
       (match build_seq_pattern raw with
        | PSeq (names, rest) ->
          let () = assert_unique (pattern_names (PSeq (names, rest))) in
          Lambda (names, rest, build_ast e)
        | _ -> err ())
     | Symbol "fn" :: ns :: body when body <> [] ->
       let err () = raise @@ TypeError "(fn [formals] body-expr ...)" in
       let raw =
         match ns with
         | Vector v -> v
         | Symbol s -> [ Symbol s ]
         | _ when is_list ns -> pair_to_list ns
         | _ -> err ()
       in
       (match build_seq_pattern raw with
        | PSeq (names, rest) ->
          let () = assert_unique (pattern_names (PSeq (names, rest))) in
          let body_ast =
            match body with
            | [ e ] -> build_ast e
            | es -> Do (List.map build_ast es)
          in
          Lambda (names, rest, body_ast)
        | _ -> err ())
     | [ Symbol "defn"; Symbol n; ns; e ] ->
       let err () = raise @@ TypeError "(defn name [formals] body)" in
       let raw =
         match ns with
         | Vector v -> v
         | Symbol s -> [ Symbol s ]
         | _ when is_list ns -> pair_to_list ns
         | _ -> err ()
       in
       (match build_seq_pattern raw with
        | PSeq (names, rest) ->
          let () = assert_unique (pattern_names (PSeq (names, rest))) in
          let lam = Lambda (names, rest, build_ast e) in
          Defexp (Val (n, lam))
        | _ -> err ())
     | Symbol "defn" :: Symbol n :: ns :: body when body <> [] ->
       let err () =
         raise @@ TypeError "(defn name [formals] body-expr ...)"
       in
       let raw =
         match ns with
         | Vector v -> v
         | Symbol s -> [ Symbol s ]
         | _ when is_list ns -> pair_to_list ns
         | _ -> err ()
       in
       (match build_seq_pattern raw with
        | PSeq (names, rest) ->
          let () = assert_unique (pattern_names (PSeq (names, rest))) in
          let body_ast =
            match body with
            | [ e ] -> build_ast e
            | es -> Do (List.map build_ast es)
          in
          let lam = Lambda (names, rest, body_ast) in
          Defexp (Val (n, lam))
        | _ -> err ())
     | [ Symbol "defmacro"; Symbol n; ns; e ] ->
       let err () = raise @@ TypeError "(defmacro name [formals] body)" in
       let raw =
         match ns with
         | Vector v -> List.map (function Symbol s -> s | _ -> err ()) v
         | Symbol s -> [ s ]
         | _ when is_list ns ->
           List.map
             (function Symbol s -> s | _ -> err ())
             (pair_to_list ns)
         | _ -> err ()
       in
       let names, rest = parse_params raw err in
       let () =
         assert_unique
           (match rest with None -> names | Some r -> r :: names)
       in
       Defexp (Val (n, Literal (Macro (names, rest, e, []))))
     | [ Symbol "apply"; fnexp; args ] ->
       Apply (build_ast fnexp, build_ast args)
     | fnexp :: args -> Call (build_ast fnexp, List.map build_ast args)
     | [] -> raise @@ ParseError "poorly formed expression")
  | Pair _ -> Literal sexp
