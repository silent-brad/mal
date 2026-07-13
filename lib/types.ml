exception SyntaxError of string
exception ParseError of string
exception NotFound of string
exception TypeError of string
exception ThisCan'tHappenError
exception UnspecifiedValue of string
exception UniqueError of string

let current_ns = ref "user"
let current_source = ref ("", 0)

type 'a env = (string * 'a option ref) list

type stream =
  { line_num : int ref
  ; col_pos : int ref
  ; mutable chr : char list
  ; is_stdin : bool
  ; source : string
  ; stm : char Lwt_stream.t
  }

type lobject =
  | Fixnum of int
  | Boolean of bool
  | Symbol of string
  | Nil
  | Pair of lobject * lobject
  | Primitive of string * (lobject list -> lobject)
  | Quote of value
  | Closure of pattern list * pattern option * exp * value env
  | String of string
  | Vector of lobject list
  | Map of (lobject * lobject) list
  | Set of lobject list
  | Keyword of string
  | Macro of name list * name option * lobject * value env

and value = lobject
and name = string

and pattern =
  | PName of name
  | PSeq of pattern list * pattern option
  | PMap of (lobject * pattern) list

and exp =
  | Literal of value
  | Var of name
  | If of exp * exp * exp
  | And of exp * exp
  | Or of exp * exp
  | Apply of exp * exp
  | Call of exp * exp list
  | Lambda of pattern list * pattern option * exp
  | Let of (pattern * exp) list * exp
  | Defexp of def
  | Do of exp list
  | LoadFile of exp

and def =
  | Val of name * exp
  | Exp of exp
