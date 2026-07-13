open Types
open Lwt.Syntax

let mkstream is_stdin source stm =
  { line_num = ref 1; col_pos = ref 0; chr = []; is_stdin; source; stm }

let mkstringstream ?(filename = "<string>") s =
  mkstream false filename (Lwt_stream.of_string s)

let mkfilestream name f =
  if f = stdin then (
    let get () = Lwt_io.read_char_opt Lwt_io.stdin in
    mkstream true "<stdin>" (Lwt_stream.from get))
  else (
    let source = In_channel.input_all f in
    mkstream false name (Lwt_stream.of_string source))

let unread_char stm c = stm.chr <- c :: stm.chr
let is_white c = c = ' ' || c = '\t' || c = '\n' || c = '\r' || c = ','
let string_of_char c = String.make 1 c

let read_char stm =
  match stm.chr with
  | [] ->
    let* copt = Lwt_stream.get stm.stm in
    (match copt with
     | None -> Lwt.fail End_of_file
     | Some c ->
       if c = '\n' then (
         stm.line_num := !(stm.line_num) + 1;
         stm.col_pos := 0)
       else
         stm.col_pos := !(stm.col_pos) + 1;
       Lwt.return c)
  | c :: rest ->
    stm.chr <- rest;
    Lwt.return c

let loc stm = !(stm.line_num), !(stm.col_pos), stm.source

let rec eat_whitespace stm =
  let* c = read_char stm in
  if is_white c then eat_whitespace stm else Lwt.return (unread_char stm c)

let error stm msg =
  let line, col, source = loc stm in
  Lwt.fail @@ SyntaxError (Printf.sprintf "%s:%d:%d: %s" source line col msg)

let rec read_sexp stm =
  let is_digit c =
    let code = Char.code c in
    code >= Char.code '0' && code <= Char.code '9'
  in
  let rec read_fixnum acc =
    let* nc = read_char stm in
    if is_digit nc then
      read_fixnum (acc ^ Char.escaped nc)
    else (
      unread_char stm nc;
      Lwt.return (Fixnum (int_of_string acc)))
  in
  let is_symstartchar =
    let is_alpha = function 'A' .. 'Z' | 'a' .. 'z' -> true | _ -> false in
    function
    | '*' | '/' | '>' | '<' | '=' | '?' | '!' | '+' | ':' | '%' | '&' | '-'
      ->
      true
    | c -> is_alpha c
  in
  let rec read_symbol () =
    let is_delimiter = function
      | '(' | ')' | '|' | '{' | '}' | '[' | ']' | ';' -> true
      | c when c = '"' -> true
      | c -> is_white c
    in
    let* nc = read_char stm in
    if is_delimiter nc then (
      unread_char stm nc; Lwt.return "")
    else
      let* rest = read_symbol () in
      Lwt.return (string_of_char nc ^ rest)
  in
  let rec read_list stm close_char =
    let* () = eat_whitespace stm in
    let* c = read_char stm in
    if c = close_char then
      Lwt.return []
    else (
      unread_char stm c;
      let* car = read_sexp stm in
      let* cdr = read_list stm close_char in
      Lwt.return (car :: cdr))
  in
  let rec eat_comment stm =
    let* c = read_char stm in
    if c = '\n' then Lwt.return () else eat_comment stm
  in
  let rec read_map stm =
    let* () = eat_whitespace stm in
    let* c = read_char stm in
    if c = '}' then
      Lwt.return (Map [])
    else (
      unread_char stm c;
      let* k = read_sexp stm in
      let* () = eat_whitespace stm in
      let* v = read_sexp stm in
      let* rest = read_map stm in
      match rest with
      | Map m -> Lwt.return (Map ((k, v) :: m))
      | _ -> raise ThisCan'tHappenError)
  in
  let read_string stm =
    let rec read_chars acc =
      let* c = read_char stm in
      if c = '"' then
        Lwt.return
          (String (String.concat "" (List.rev (List.map string_of_char acc))))
      else if c = '\\' then
        let* nc = read_char stm in
        let esc =
          match nc with
          | 'n' -> '\n'
          | 't' -> '\t'
          | '\\' -> '\\'
          | '"' -> '"'
          | c -> c
        in
        read_chars (esc :: acc)
      else
        read_chars (c :: acc)
    in
    read_chars []
  in
  let* () = eat_whitespace stm in
  let* c = read_char stm in
  if c = ';' then
    let* () = eat_comment stm in
    read_sexp stm
  else if c = '-' then
    let* nc = read_char stm in
    if is_digit nc then
      read_fixnum ("-" ^ Char.escaped nc)
    else (
      unread_char stm nc;
      let* sym = read_symbol () in
      Lwt.return (Symbol (string_of_char c ^ sym)))
  else if is_symstartchar c then
    let* sym = read_symbol () in
    let s = string_of_char c ^ sym in
    match s with
    | _ when String.starts_with s ~prefix:"::" ->
      let name = String.sub s 2 (String.length s - 2) in
      Lwt.return @@ Keyword (!Types.current_ns ^ "/" ^ name)
    | _ when String.starts_with s ~prefix:":" ->
      let name = String.sub s 1 (String.length s - 1) in
      Lwt.return @@ Keyword name
    | "true" -> Lwt.return (Boolean true)
    | "false" -> Lwt.return (Boolean false)
    | "nil" -> Lwt.return Nil
    | _ -> Lwt.return (Symbol s)
  else if c = '~' then
    let* e = read_sexp stm in
    Lwt.return @@ Pair (Symbol "unquote", Pair (e, Nil))
  else if c = '`' then
    let* e = read_sexp stm in
    Lwt.return @@ Pair (Symbol "quasiquote", Pair (e, Nil))
  else if c = ',' then
    let* nc = read_char stm in
    if nc = '@' then
      let* e = read_sexp stm in
      Lwt.return @@ Pair (Symbol "unquote-splicing", Pair (e, Nil))
    else (
      unread_char stm nc;
      let* e = read_sexp stm in
      Lwt.return @@ Pair (Symbol "unquote", Pair (e, Nil)))
  else if c = '@' then
    let* e = read_sexp stm in
    Lwt.return @@ Pair (Symbol "deref", Pair (e, Nil))
  else if c = '(' then
    let* elems = read_list stm ')' in
    Lwt.return @@ List.fold_right (fun car cdr -> Pair (car, cdr)) elems Nil
  else if c = '[' then
    let* elems = read_list stm ']' in
    Lwt.return @@ Vector elems
  else if c = '{' then
    read_map stm
  else if c = '"' then
    read_string stm
  else if is_digit c then
    read_fixnum (Char.escaped c)
  else if c = '#' then
    let* x = read_char stm in
    match x with
    | '(' ->
      unread_char stm x;
      let* body = read_sexp stm in
      let rec collect_max n = function
        | Symbol "%" -> max n 1
        | Symbol s when String.length s > 1 && s.[0] = '%' ->
          (try
             let i = int_of_string (String.sub s 1 (String.length s - 1)) in
             max n i
           with
           | _ -> n)
        | Pair (a, b) -> collect_max (collect_max n a) b
        | _ -> n
      in
      let max_n = collect_max 0 body in
      let args =
        List.init max_n (fun i -> Symbol ("%" ^ string_of_int (i + 1)))
      in
      let rec rewrite = function
        | Symbol "%" -> Symbol "%1"
        | Pair (a, b) -> Pair (rewrite a, rewrite b)
        | other -> other
      in
      let body' = rewrite body in
      Lwt.return (Pair (Symbol "fn", Pair (Vector args, Pair (body', Nil))))
    | '{' ->
      let* elems = read_list stm '}' in
      Lwt.return (Set elems)
    | '_' ->
      let* _ = read_sexp stm in
      read_sexp stm
    | _ -> error stm ("Invalid dispatch macro: #" ^ Char.escaped x)
  else if c = '\'' then
    let* e = read_sexp stm in
    Lwt.return (Pair (Symbol "quote", Pair (e, Nil)))
  else
    error stm ("Unexpected char " ^ Char.escaped c)

let read_sexp_with_loc stm =
  let* () = eat_whitespace stm in
  let line = !(stm.line_num) in
  let* sexp = read_sexp stm in
  Lwt.return (sexp, stm.source, line)
