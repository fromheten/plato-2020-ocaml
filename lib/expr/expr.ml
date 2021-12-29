type position = (* source position - index *)
  int * int

type 'a pattern =
  | PSym of position * string
  | PTag of position * string * 'a

type expr =
  (* Beauty and Virtue *)
  | Lam of position * (expr pattern * expr) list
  | App of position * expr * expr
  | Sym of position * string
  (* Basic types *)
  | U8 of position * int
  | String of position * string
  | Tuple of position * expr list
  (* pair, sum type, nple, call it what you want *)
  | Unit of position
  | Vector of position * expr list
  | Set of position * expr list
  | Dict of position * (expr * expr) list
  | Ann of position * Type.Type.typ * expr (* Annotation *)
  | Match of position * expr * (expr pattern * expr) list
  (* Let *)
  | Let of position * string * expr * expr
  | Letrec of position * string * expr * expr
  (* Enum *)
  | TaggedValue of string * Type.Type.typ * expr (* tag, enum, tagged value *)
  | Enum of Type.Type.typ
  (* invariant: must be TyTagUnion, therefore doesnt need a pos *)
  (* Forall, Λ *)
  | TypeDef of position * string list * expr

let is_symbol_char c =
  not
    (List.exists
       (fun x -> x = c)
       [ ' '
       ; '\''
       ; '"'
       ; '\t'
       ; '\n'
       ; '#'
       ; '('
       ; ')'
       ; '<'
       ; '>'
       ; '['
       ; ']'
       ; '{'
       ; '}'
       ] )


let string_of_sym (s : string) : string =
  if List.exists (Util.comp not is_symbol_char) (Util.char_list s)
  then "\"" ^ s ^ "\""
  else s


let string_of_pattern string_of_value : expr pattern -> string = function
  | PSym (_pos, s) -> string_of_sym s
  | PTag (_pos, tag, value) ->
    "(" ^ string_of_sym tag ^ " " ^ string_of_value value ^ ")"


let rec string_of_expr gensym_env : expr -> string = function
  | Let (_pos, name, definition, body) ->
    Printf.sprintf
      "(let %s %s\n  %s)"
      name
      (string_of_expr gensym_env definition)
      (string_of_expr gensym_env body)
  | Letrec (_pos, name, definition, body) ->
    Printf.sprintf
      "(letrec %s %s\n  %s)"
      name
      (string_of_expr gensym_env definition)
      (string_of_expr gensym_env body)
  | U8 (_pos, i) -> "(u8 " ^ string_of_int i ^ ")"
  | Sym (_pos, s) -> string_of_sym s
  | Lam (_pos, patterns_exprs) ->
    "(λ "
    ^ String.concat
        ""
        (List.map
           (function
             | PTag (_ptag_pos, name, child), expr ->
               "( "
               ^ name
               ^ " "
               ^ string_of_expr gensym_env child
               ^ ") "
               ^ string_of_expr gensym_env expr
             | PSym (_psym_pos, x), expr ->
               string_of_expr gensym_env (Sym (_psym_pos, x))
               ^ " "
               ^ string_of_expr gensym_env expr )
           patterns_exprs )
    ^ ")"
  | App (_pos, e0, e1) ->
    "("
    ^ string_of_expr gensym_env e0
    ^ " "
    ^ string_of_expr gensym_env e1
    ^ ")"
  | Match (_pos, x, cases) ->
    "(match "
    ^ string_of_expr gensym_env x
    ^ String.concat
        ""
        (List.map
           (fun (pattern, expr) ->
             " "
             ^ string_of_pattern (string_of_expr gensym_env) pattern
             ^ " "
             ^ string_of_expr gensym_env expr )
           cases )
    ^ ")"
  | String (_pos, s) -> "\"" ^ s ^ "\""
  | Tuple (_pos, exprs) ->
    "<" ^ String.concat " " (List.map (string_of_expr gensym_env) exprs) ^ ">"
  | Unit _pos -> "<>"
  | Vector (_pos, exprs) ->
    Printf.sprintf
      "[%s]"
      (String.concat " " (List.map (string_of_expr gensym_env) exprs))
  | Set (_pos, exprs) ->
    Printf.sprintf
      "#{%s}#"
      (String.concat " " (List.map (string_of_expr gensym_env) exprs))
  | Ann (_pos, t, e) ->
    Printf.sprintf
      "(Ann %s %s)"
      (Type.Type.to_string gensym_env t)
      (string_of_expr gensym_env e)
  | Dict (_pos, keys_and_vals) ->
    Printf.sprintf
      "{%s}"
      (String.concat
         " "
         (List.map
            (fun (key, value) ->
              Printf.sprintf
                "%s %s"
                (string_of_expr gensym_env key)
                (string_of_expr gensym_env value) )
            keys_and_vals ) )
  | TaggedValue (name, _enum, value) ->
    Printf.sprintf "(%s %s)" name (string_of_expr gensym_env value)
  | Enum t -> Type.Type.to_string gensym_env t
  | TypeDef (_pos, args, child_expr) ->
    "(type ["
    ^ String.trim (String.concat " " args)
    ^ "%s"
    ^ "] "
    ^ string_of_expr gensym_env child_expr
    ^ ")"
