type typ =
  (* Two base types, just to have something to play with *)
  | TUnit
  | TInt
  | TEnum of string * (string * typ) list
  | TSym of string

type expr =
  | Unit
  | Int of int
  | TaggedValue of string * typ * expr (* tag, enum, tagged value *)
  | Let of (string * expr) list * expr
  | Enum of typ
  | Sym of string

let rec eval (ctx: (string * expr) list) expr =
  match expr with
  | Unit -> expr
  | Int i -> expr
  | TaggedValue (name, enum, value) -> expr
  | Let ((name, value) :: rest, then_expr) ->
    eval ((name, value) :: ctx) then_expr
  | Let ([], _) -> failwith "Let with no cases makes no sense"
  | Enum t -> expr
  | Sym s -> List.assoc s ctx

let rec typeof (ctx: (string * typ) list) expr =
  match expr with
  | Unit -> TUnit
  | Int _i -> TInt
  | TaggedValue (tag, TEnum (enum_name, cases), value) ->
    (match (List.assoc_opt tag cases) with
     | Some t when typeof ctx value = t -> TEnum (enum_name, cases)
     | Some _t -> failwith (Printf.sprintf "Tag %s given wrong type for enum %s" tag enum_name)
     | None -> failwith (Printf.sprintf "Tag %s not found in Enum %s" tag enum_name))
  | TaggedValue (_name, (TSym tsym), _value) ->
    typeof
      ctx
      (TaggedValue (_name, (List.assoc tsym ctx), _value))
  | Let ([], then_expr) ->
    typeof ctx then_expr
  | Let ((name, definition) :: rest_of_definitions, then_expr) ->
    let new_ctx = (name, typeof ctx definition) :: ctx in
    typeof new_ctx (Let (rest_of_definitions, then_expr))
  | Enum t -> t
  | Sym s -> List.assoc s ctx
  | TaggedValue (_, (TUnit
                    |TInt), _) ->
    failwith "A Tagged value must be tagged with an Enum"

let with_stdlib expr = Let (["Bool", (Enum (TEnum ("Bool", [("True", TUnit)
                                                           ;("False", TUnit)])))
                            ;"Option", (Enum (TEnum ("Option", ["Some", TInt
                                                               ;"None", TUnit])))],
                            expr);;
(* Examples: try them out in the repl *)
(*
 * typeof [] (with_stdlib (TaggedValue ("True", TSym "Bool", Int 1))) (\* => Errors, expected Unit got Int *\)
 * typeof [] (with_stdlib (TaggedValue ("Some", TSym "Option", Int 1337))) (\* => Succeeds, tag name belongs in Option, and Int is correct *\) *)
