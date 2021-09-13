type position = (* source position - index *)
  int * int

type 'a pattern =
  | PSym of position * string
  | PTag of position * string * 'a

type expr =
  | Lam of position * (expr pattern * expr) list
  | App of position * expr * expr
  | Sym of position * string
  | U8 of position * int
  | String of position * string
  | Tuple of position * expr list          (* pair, sum type, nple, call it what you want *)
  | Unit of position
  | Vector of position * expr list
  | Set of position * expr list
  | Ann of position * Type_infer.Type.t * expr
  | Dict of position * (expr * expr) list
  | Match of position * expr * (expr pattern * expr) list
  | Let of position * string * expr * expr
  | Letrec of position * string * expr * expr
