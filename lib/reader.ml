open Types

let read_char stm =
  match stm.chr with
  | [] ->
    let c = input_char stm.chan in
    if c = '\n' then (
      let _ = stm.line_num <- stm.line_num + 1 in
      c)
    else
      c
  | c :: rest ->
    let _ = stm.chr <- rest in
    c

let unread_char stm c = stm.chr <- c :: stm.chr
let is_white c = c = ' ' || c = '\t' || c = '\n'

let rec eat_whitespace stm =
  let c = read_char stm in
  if is_white c then eat_whitespace stm else unread_char stm c

let string_of_char c = String.make 1 c

let rec read_sexp stm =
  let is_digit c =
    let code = Char.code c in
    code >= Char.code '0' && code <= Char.code '9'
  in
  let rec read_fixnum acc =
    let nc = read_char stm in
    if is_digit nc then
      read_fixnum (acc ^ Char.escaped nc)
    else (
      let _ = unread_char stm nc in
      Fixnum (int_of_string acc))
  in
  let is_symstartchar =
    let is_alpha = function 'A' .. 'Z' | 'a' .. 'z' -> true | _ -> false in
    function
    | '*' | '/' | '>' | '<' | '=' | '?' | '!' | '-' | '+' -> true
    | c -> is_alpha c
  in
  let rec read_symbol () =
    let is_delimiter = function
      | '(' | ')' | '|' | '{' | '}' | ';' -> true
      | c when c = '"' -> true
      | c -> is_white c
    in
    let nc = read_char stm in
    if is_delimiter nc then (
      let _ = unread_char stm nc in
      "")
    else
      string_of_char nc ^ read_symbol ()
  in
  let rec read_list stm =
    eat_whitespace stm;
    let c = read_char stm in
    if c = ')' then
      Nil
    else (
      let _ = unread_char stm c in
      let car = read_sexp stm in
      let cdr = read_list stm in
      Pair (car, cdr))
  in
  let rec eat_comment stm =
    if read_char stm = '\n' then () else eat_comment stm
  in
  eat_whitespace stm;
  let c = read_char stm in
  if c = ';' then (
    eat_comment stm; read_sexp stm)
  else if is_symstartchar c then
    Symbol (string_of_char c ^ read_symbol ())
  else if c = '(' then
    read_list stm
  else if is_digit c || c = '~' then
    read_fixnum (Char.escaped (if c = '~' then '-' else c))
  else if c = '#' then (
    match
      read_char stm
    with
    | 't' -> Boolean true
    | 'f' -> Boolean false
    | x -> raise @@ SyntaxError ("Invalid boolean literal " ^ Char.escaped x))
  else if c = '\'' then
    Quote (read_sexp stm)
  else
    raise @@ SyntaxError ("Unexpected char " ^ Char.escaped c)
