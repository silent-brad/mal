open Types
open Env
open Printer

let numprim name op =
  ( name
  , function
    | [ Fixnum a; Fixnum b ] -> Fixnum (op a b)
    | _ -> raise @@ TypeError ("(" ^ name ^ " int int)") )

let cmpprim name op =
  ( name
  , function
    | [ Fixnum a; Fixnum b ] -> Boolean (op a b)
    | _ -> raise @@ TypeError ("(" ^ name ^ " int int)") )

let newprim acc (name, func) = bind (name, Primitive (name, func), acc)

let rec prim_list = function
  | [] -> Nil
  | car :: cdr -> Pair (car, prim_list cdr)

let prim_pair = function
  | [ a; b ] -> Pair (a, b)
  | _ -> raise @@ TypeError "(pair a b)"

let prim_car = function
  | [ Pair (car, _) ] -> car
  | [ Vector v ] -> if v <> [] then List.hd v else Nil
  | [ Nil ] -> Nil
  | [ e ] -> raise @@ TypeError ("(car pair) got " ^ string_val e)
  | _ -> raise @@ TypeError "(car single-arg)"

let prim_cdr = function
  | [ Pair (_, cdr) ] -> cdr
  | [ Vector v ] -> if List.length v > 1 then Vector (List.tl v) else Nil
  | [ Nil ] -> Nil
  | [ e ] -> raise @@ TypeError ("(cdr pair) got " ^ string_val e)
  | _ -> raise @@ TypeError "(cdr single-arg)"

let prim_eq = function
  | [ a; b ] -> Boolean (a = b)
  | _ -> raise @@ TypeError "(= a b)"

let prim_not_eq = function
  | [ a; b ] -> Boolean (a <> b)
  | _ -> raise @@ TypeError "(not= a b)"

let prim_atomp = function
  | [ Nil ] -> Boolean true
  | [ Pair (_, _) ] -> Boolean false
  | [ _ ] -> Boolean true
  | _ -> raise @@ TypeError "(atom? single-arg)"

let prim_symp = function
  | [ Symbol _ ] -> Boolean true
  | [ _ ] -> Boolean false
  | _ -> raise @@ TypeError "(sym? single-arg)"

let prim_symbolp = function
  | [ Symbol _ ] -> Boolean true
  | [ _ ] -> Boolean false
  | _ -> raise @@ TypeError "(symbol? x)"

let prim_keywordp = function
  | [ Keyword _ ] -> Boolean true
  | [ _ ] -> Boolean false
  | _ -> raise @@ TypeError "(keyword? x)"

let prim_numberp = function
  | [ Fixnum _ ] -> Boolean true
  | [ _ ] -> Boolean false
  | _ -> raise @@ TypeError "(number? x)"

let prim_stringp = function
  | [ String _ ] -> Boolean true
  | [ _ ] -> Boolean false
  | _ -> raise @@ TypeError "(string? x)"

let prim_vectorp = function
  | [ Vector _ ] -> Boolean true
  | [ _ ] -> Boolean false
  | _ -> raise @@ TypeError "(vector? x)"

let prim_mapp = function
  | [ Map _ ] -> Boolean true
  | [ _ ] -> Boolean false
  | _ -> raise @@ TypeError "(map? x)"

let prim_listp = function
  | [ e ] -> Boolean (is_list e)
  | _ -> raise @@ TypeError "(list? x)"

let prim_seqp = function
  | [ Nil ] | [ Pair _ ] | [ Vector _ ] -> Boolean true
  | [ _ ] -> Boolean false
  | _ -> raise @@ TypeError "(seq? x)"

let prim_getchar = function
  | [] ->
    (try Fixnum (int_of_char (input_char stdin)) with
     | End_of_file -> Fixnum (-1))
  | _ -> raise @@ TypeError "(getchar)"

let prim_print = function
  | [ v ] ->
    print_string (string_val v);
    Symbol "ok"
  | _ -> raise @@ TypeError "(print val)"

let prim_println = function
  | [ v ] ->
    print_endline (string_val v);
    Symbol "ok"
  | _ -> raise @@ TypeError "(println val)"

let prim_readline = function
  | [] -> (try String (read_line ()) with End_of_file -> Nil)
  | _ -> raise @@ TypeError "(read-line)"

let prim_itoc = function
  | [ Fixnum i ] -> Symbol (string_of_char (char_of_int i))
  | _ -> raise @@ TypeError "(itoc int)"

let prim_cat = function
  | [ Symbol a; Symbol b ] -> Symbol (a ^ b)
  | _ -> raise @@ TypeError "(cat sym sym)"

let prim_str = function
  | args ->
    let coerce = function String s -> s | other -> string_val other in
    String (String.concat "" (List.map coerce args))

let prim_vector = function args -> Vector args

let prim_hashmap = function
  | args ->
    let rec pairs = function
      | [] -> []
      | a :: b :: rest -> (a, b) :: pairs rest
      | _ -> raise @@ TypeError "(hash-map k0 v0 ...)"
    in
    Map (pairs args)

let prim_seq = function
  | [ Vector v ] -> List.fold_right (fun x acc -> Pair (x, acc)) v Nil
  | [ (Pair _ as lst) ] when is_list lst -> lst
  | [ Nil ] -> Nil
  | _ -> raise @@ TypeError "(seq coll)"

let prim_get = function
  | [ Map m; key ] -> (try List.assoc key m with Not_found -> Nil)
  | [ Vector v; Fixnum i ] ->
    if i >= 0 && i < List.length v then List.nth v i else Nil
  | _ -> raise @@ TypeError "(get coll key)"

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

let prim_assoc = function
  | [ Map m; key; value ] -> Map ((key, value) :: m)
  | _ -> raise @@ TypeError "(assoc m key value)"

let gensym_counter = ref 0

let prim_gensym = function
  | [] ->
    let n = !gensym_counter in
    incr gensym_counter;
    Symbol ("G_" ^ string_of_int n)
  | _ -> raise (TypeError "(gensym)")

let prim_slurp = function
  | [ String s ] -> String (In_channel.with_open_text s In_channel.input_all)
  | _ -> raise @@ TypeError "(slurp path)"

let prim_spit = function
  | [ String path; String content ] ->
    Out_channel.with_open_text path (fun oc ->
      Out_channel.output_string oc content);
    Symbol "ok"
  | _ -> raise @@ TypeError "(spit path content)"

let prim_deref = function
  | [ x ] -> x
  | _ -> raise @@ TypeError "(deref ref)"

let prim_set = function args -> Set args

let prim_in_ns = function
  | [ Symbol ns ] ->
    current_ns := ns;
    Symbol ns
  | _ -> raise @@ TypeError "(in-ns 'name)"

let prim_ns = function
  | [] -> Symbol !current_ns
  | _ -> raise @@ TypeError "(*ns*)"
