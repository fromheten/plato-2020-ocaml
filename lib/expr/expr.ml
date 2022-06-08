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
  | Ann of position * Hmtype.typ * expr (* Annotation *)
  | Match of position * expr * (expr pattern * expr) list
  (* Let *)
  | Let of position * string * expr * expr
  | Letrec of position * string * expr * expr
  (* Enum *)
  | TaggedValue of string * Hmtype.typ * expr (* tag, enum, tagged value *)
  | Enum of Hmtype.typ
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
    let typ_string = Hmtype.string_of_typ t in
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
  | Enum t -> (state, Hmtype.string_of_typ t)
  | TypeDef (_pos, args, child_expr) ->
    let state, child_expr_string = string_of_expr state child_expr in
    ( state
    , "(type ["
      ^ String.trim (String.concat " " args)
      ^ "%s"
      ^ "] "
      ^ child_expr_string
      ^ ")" )


module VarSet = Set.Make (String)

let rec free_vars (expr : expr) =
  match expr with
  | U8 (_, _) -> VarSet.empty
  | String (_, _) -> VarSet.empty
  | Unit _ -> VarSet.empty
  | Sym (_, s) -> VarSet.add s VarSet.empty
  | App (_, f, x) -> VarSet.union (free_vars f) (free_vars x)
  | Lam (_, (PSym (_, x), body) :: _) ->
    VarSet.filter (( = ) x) (free_vars body)
  | Lam (_, (PTag (_, _, _), _) :: _) -> failwith "PTag free_vars not done"
  | Lam (_, []) -> failwith "PTag free_vars not done"
  | Let (_, var, value, body) ->
    let vars = VarSet.add var VarSet.empty in
    let vals = [ value ] in
    let vals_free_vals =
      List.fold_left VarSet.union (free_vars body) (List.map free_vars vals)
    in
    VarSet.diff vals_free_vals vars
  | Tuple (_, _)
  | Vector (_, _)
  | Set (_, _)
  | Dict (_, _)
  | Ann (_, _, _)
  | Match (_, _, _)
  | Letrec (_, _, _, _)
  | TaggedValue (_, _, _)
  | Enum _
  | TypeDef (_, _, _) ->
    failwith "Haven't implemented free_vars of fancy expressions"


let rec infer_type (env : Hmtype.typ_env) (exp : expr) :
    Hmtype.typ_env * Hmtype.typ =
  match exp with
  | Match (_, _, _)
  | Letrec (_, _, _, _)
  | TaggedValue (_, _, _)
  | Enum _
  | TypeDef (_, _, _) ->
    failwith "A bunch of type inferrence things not done"
  | Ann (_, t, e) ->
    let _env, e_type = infer_type env e in
    ( match Hmtype.unify t e_type with
    | Ok env -> (env, e_type)
    | Error unify_err ->
      failwith
        (Printf.sprintf
           "Ann invariant untrue - \n\
            expression %s is NOT of \n\
            type %s, but is rather of \n\
            type %s\n\n\
           \           Unification err: %s           "
           (snd (string_of_expr (-1, 'a') e))
           (Hmtype.string_of_typ t)
           (Hmtype.string_of_typ e_type)
           (Hmtype.string_of_unify_err unify_err) ) )
  | U8 (_, _) -> ([], Hmtype.TypeConstant Integer)
  | String (_, _) -> ([], TypeConstant String)
  | Unit (_, _) -> ([], TypeConstant Unit)
  | Tuple (_, _children) ->
    failwith "haven't yet implemented typecheck for tuples"
  | Vector (_, []) ->
    (env, Hmtype.TypeConstant (Vector (Hmtype.gen_type_variable "")))
  | Vector (_, first_child :: children) ->
    let children_types : Hmtype.typ list =
      List.map (Util.comp snd (infer_type env)) (first_child :: children)
    in
    ( match Hmtype.unify_many children_types [] [] with
    | Ok env ->
      let env, first_child_typ = infer_type env first_child in
      (env, Hmtype.TypeConstant (Vector first_child_typ))
    | Error es ->
      failwith
        ( "Vector infer errors: "
        ^ String.concat "\n" (List.map Hmtype.string_of_unify_err es) ) )
  | Set (_, _children) -> failwith "haven't yet implemented typecheck for sets"
  | Dict (_, _children) ->
    failwith "haven't yet implemented typecheck for dicts"
  | Sym (_, v) ->
    ( match List.assoc_opt v env with
    | Some t -> ([], Hmtype.instantiate t)
    | None ->
      failwith ("Unbound variable: " ^ snd (string_of_expr (-1, 'a') exp)) )
  | Lam (_pos, (PSym (_, arg), body) :: _) ->
    let arg_t = Hmtype.gen_type_variable arg in
    let env' = (arg, arg_t) :: env in
    let substitutions, body_t = infer_type env' body in
    ( substitutions
    , Hmtype.replace_substitutions
        substitutions
        (TypeApp [ TypeConstant Arrow; arg_t; body_t ]) )
  | Lam (_, []) -> failwith "Can't check a lambda without cases?"
  | Lam (_, (PTag (_, _, _), _) :: _) -> failwith "not done"
  | App (_, fn, arg) ->
    let res_t =
      match fn with
      | Sym (_, fn_name) -> Hmtype.gen_type_variable (fn_name ^ "-result")
      | _ -> Hmtype.gen_type_variable ""
    in
    let substs1, fun_t = infer_type env fn in
    let substs2, arg_t =
      infer_type (Hmtype.replace_substitutions_env substs1 env) arg
    in
    ( match
        Hmtype.unify
          (Hmtype.replace_substitutions substs2 fun_t)
          (TypeApp [ TypeConstant Arrow; arg_t; res_t ])
      with
    | Ok subst3 ->
      ( List.fold_left Hmtype.compose_substitutions subst3 [ substs2; substs1 ]
      , Hmtype.replace_substitutions subst3 res_t )
    | Error e -> failwith (Hmtype.string_of_unify_err e) )
  | Let (_, var, value, body) ->
    (* If var is referred to in value - i.e. if recursion happens *)
    if VarSet.mem var (free_vars value)
    then
      let var_tv = Hmtype.gen_type_variable var in
      let new_env = (var, var_tv) :: env in
      let s1, t1 = infer_type new_env value in
      match Hmtype.unify var_tv t1 with
      | Ok s1' ->
        let s2, t2 =
          infer_type
            (Hmtype.replace_substitutions_env
               (Hmtype.compose_substitutions s1 s1')
               new_env )
            body
        in
        (Hmtype.compose_substitutions s2 s1, t2)
      | Error e -> failwith (Hmtype.string_of_unify_err e)
    else
      let s1, t1 = infer_type env value in
      let t' = Hmtype.generalize (Hmtype.replace_substitutions_env s1 env) t1 in
      let env' = (var, t') :: env in
      let s2, t2 = infer_type (Hmtype.replace_substitutions_env s1 env') body in
      (Hmtype.compose_substitutions s2 s1, t2)


let infer env (exp : expr) : Hmtype.typ =
  match Ok (infer_type env exp) with
  | Ok (substitutions, t) ->
    Hmtype.generalize env (Hmtype.replace_substitutions substitutions t)
  | _ -> failwith "infer_type error"
