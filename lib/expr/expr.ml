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


(* TODO This depends on string_of_value being stateful *)
let string_of_pattern string_of_value : expr pattern -> string = function
  | PSym (_pos, s) -> string_of_sym s
  | PTag (_pos, tag, value) ->
    "(" ^ string_of_sym tag ^ " " ^ string_of_value value ^ ")"


let string_of_pattern_pure state string_of_value = function
  | PSym (_pos, s) -> (state, string_of_sym s)
  | PTag (_pos, tag, value) ->
    let state, value_string = string_of_value state value in
    (state, "(" ^ string_of_sym tag ^ " " ^ value_string ^ ")")


let rec string_of_expr (state : 'state) : expr -> 'state * string = function
  | Let (_pos, name, definition, body) ->
    let state, definition_string = string_of_expr state definition in
    let state, body_string = string_of_expr state body in
    ( state
    , Printf.sprintf "(let %s %s\n  %s)" name definition_string body_string )
  | Letrec (_pos, name, definition, body) ->
    let state, definition_string = string_of_expr state definition in
    let state, body_string = string_of_expr state body in
    ( state
    , Printf.sprintf "(letrec %s %s\n  %s)" name definition_string body_string
    )
  | U8 (_pos, i) -> (state, "(u8 " ^ string_of_int i ^ ")")
  | Sym (_pos, s) -> (state, string_of_sym s)
  | Lam (_pos, patterns_exprs) ->
    let state, strings =
      State.map
        (fun state -> function
          | PTag (_ptag_pos, name, child), expr ->
            let state, child_string = string_of_expr state child in
            let state, expr_string = string_of_expr state expr in
            (state, "( " ^ name ^ " " ^ child_string ^ ") " ^ expr_string)
          | PSym (_psym_pos, x), expr ->
            let state, x_string = string_of_expr state (Sym (_psym_pos, x)) in
            let state, expr_string = string_of_expr state expr in
            (state, x_string ^ " " ^ expr_string) )
        []
        state
        patterns_exprs
    in
    (state, "(λ " ^ String.concat "" strings ^ ")")
  | App (_pos, e0, e1) ->
    let state, e0_string = string_of_expr state e0 in
    let state, e1_string = string_of_expr state e1 in
    (state, "(" ^ e0_string ^ " " ^ e1_string ^ ")")
  | Match (_pos, x, cases) ->
    let state, x_string = string_of_expr state x in
    let state, cases_strings =
      State.map
        (fun state (pattern, expr) ->
          let state, pattern_string =
            string_of_pattern_pure state string_of_expr pattern
          in
          let state, expr_string = string_of_expr state expr in
          (state, " " ^ pattern_string ^ " " ^ expr_string) )
        []
        state
        cases
    in

    (state, "(match " ^ x_string ^ String.concat "" cases_strings ^ ")")
  | String (_pos, s) -> (state, "\"" ^ s ^ "\"")
  | Tuple (_pos, exprs) ->
    let state, exprs_strings =
      State.map (fun state -> string_of_expr state) [] state exprs
    in
    (state, "<" ^ String.concat " " exprs_strings ^ ">")
  | Unit _pos -> (state, "<>")
  | Vector (_pos, exprs) ->
    let state, exprs_strings =
      State.map (fun state -> string_of_expr state) [] state exprs
    in
    (state, Printf.sprintf "[%s]" (String.concat " " exprs_strings))
  | Set (_pos, exprs) ->
    let state, exprs_strings =
      State.map (fun state -> string_of_expr state) [] state exprs
    in
    (state, Printf.sprintf "#{%s}#" (String.concat " " exprs_strings))
  | Ann (_pos, t, e) ->
    let state, typ_string = Type.string_of_typ state t in
    let state, expr_string = string_of_expr state e in
    (state, Printf.sprintf "(: %s %s)" typ_string expr_string)
  | Dict (_pos, keys_and_vals) ->
    let state, keyvalue_strings =
      State.map
        (fun state (key, value) ->
          let state, key_string = string_of_expr state key in
          let state, value_string = string_of_expr state value in
          (state, Printf.sprintf "%s %s" key_string value_string) )
        []
        state
        keys_and_vals
    in
    (state, Printf.sprintf "{%s}" (String.concat " " keyvalue_strings))
  | TaggedValue (name, _enum, value) ->
    let state, value_string = string_of_expr state value in
    (state, Printf.sprintf "(%s %s)" name value_string)
  | Enum t -> Type.string_of_typ state t
  | TypeDef (_pos, args, child_expr) ->
    let state, child_expr_string = string_of_expr state child_expr in
    ( state
    , "(type ["
      ^ String.trim (String.concat " " args)
      ^ "%s"
      ^ "] "
      ^ child_expr_string
      ^ ")" )
