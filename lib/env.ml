open Types

let string_of_char c = String.make 1 c

let rec lookup = function
  | n, [] -> raise @@ NotFound n
  | n, (n', v) :: _ when n = n' ->
    (match !v with Some v' -> v' | None -> raise @@ UnspecifiedValue n)
  | n, (n', _) :: bs -> lookup (n, bs)

let bind (n, v, e) = (n, ref (Some v)) :: e
let mkloc _ = ref None

let bindloc ((n, vor, e) : name * 'a option ref * 'a env) : 'a env =
  (n, vor) :: e

let bindlist ns vs env =
  List.fold_left2 (fun acc n v -> bind (n, v, acc)) env ns vs

let bindloclist ns vs env =
  List.fold_left2 (fun acc n v -> bindloc (n, v, acc)) env ns vs

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
  List.fold_right (fun (n, v) acc -> bindloc (n, v, acc)) newenv oldenv
