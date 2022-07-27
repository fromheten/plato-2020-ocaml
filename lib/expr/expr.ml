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
  (* Let *)
  | Let of position * string * expr * expr
  | Letrec of position * string * expr * expr
  | IfThenElse of position * expr * expr * expr
  | Bool of position * bool

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


let rec string_of_expr : expr -> string = function
  | Let (_pos, name, definition, body) ->
    let definition_string = string_of_expr definition in
    let body_string = string_of_expr body in
    Printf.sprintf "(let %s %s\n  %s)" name definition_string body_string
  | Letrec (_pos, name, definition, body) ->
    let definition_string = string_of_expr definition in
    let body_string = string_of_expr body in
    Printf.sprintf "(letrec %s %s\n  %s)" name definition_string body_string
  | U8 (_pos, i) -> "(u8 " ^ string_of_int i ^ ")"
  | Sym (_pos, s) -> string_of_sym s
  | Lam (_pos, patterns_exprs) ->
    let strings =
      List.map
        (function
          | PTag (_ptag_pos, name, child), expr ->
            let child_string = string_of_expr child in
            let expr_string = string_of_expr expr in
            "( " ^ name ^ " " ^ child_string ^ ") " ^ expr_string
          | PSym (_psym_pos, x), expr ->
            let x_string = string_of_expr (Sym (_psym_pos, x)) in
            let expr_string = string_of_expr expr in
            x_string ^ " " ^ expr_string )
        patterns_exprs
    in
    "(λ " ^ String.concat "" strings ^ ")"
  | App (_pos, e0, e1) ->
    let e0_string = string_of_expr e0 in
    let e1_string = string_of_expr e1 in
    "(" ^ e0_string ^ " " ^ e1_string ^ ")"
  | String (_pos, s) -> "\"" ^ s ^ "\""
  | Tuple (_pos, exprs) ->
    let exprs_strings = List.map string_of_expr exprs in
    "<" ^ String.concat " " exprs_strings ^ ">"
  | Unit _pos -> "<>"
  | Vector (_pos, exprs) ->
    let exprs_strings = List.map string_of_expr exprs in
    Printf.sprintf "[%s]" (String.concat " " exprs_strings)
  | Set (_pos, exprs) ->
    let exprs_strings = List.map string_of_expr exprs in
    Printf.sprintf "#{%s}#" (String.concat " " exprs_strings)
  | Ann (_pos, t, e) ->
    let typ_string = Hmtype.string_of_typ t in
    let expr_string = string_of_expr e in
    Printf.sprintf "(: %s %s)" typ_string expr_string
  | Dict (_pos, keys_and_vals) ->
    let keyvalue_strings =
      List.map
        (fun (key, value) ->
          let key_string = string_of_expr key in
          let value_string = string_of_expr value in
          Printf.sprintf "%s %s" key_string value_string )
        keys_and_vals
    in
    Printf.sprintf "{%s}" (String.concat " " keyvalue_strings)
  | IfThenElse (_pos, cond_e, then_e, else_e) ->
    let cond_s = string_of_expr cond_e in
    let then_s = string_of_expr then_e in
    let else_s = string_of_expr else_e in
    Printf.sprintf "(if %s %s %s)" cond_s then_s else_s
  | Bool (_, true) -> "C:True"
  | Bool (_, false) -> "C:False"


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
  | Letrec (_, _, _, _) ->
    failwith "Haven't implemented free_vars of fancy expressions"
  | IfThenElse (_pos, cond_e, then_e, else_e) ->
    VarSet.union
      (VarSet.union (free_vars cond_e) (free_vars then_e))
      (free_vars else_e)
  | Bool _ -> VarSet.empty


let rec infer_type (env : Hmtype.typ_env) (exp : expr) :
    Hmtype.typ_env * Hmtype.typ =
  match exp with
  | Letrec (_, _, _, _) -> failwith "A bunch of type inferrence things not done"
  | Ann (_, t, e) ->
    (* Util.debugprint "In Ann" []; *)
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
           (string_of_expr e)
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
    | None -> failwith ("Unbound variable: " ^ string_of_expr exp) )
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
    let fn_subst, fun_t = infer_type env fn in
    let arg_subst, arg_t =
      infer_type (Hmtype.replace_substitutions_env fn_subst env) arg
    in
    (* Util.debugprint
     *   "In App"
     *   [ ("env", Hmtype.show_typ_env env)
     *   ; ("fn", string_of_expr fn)
     *   ; ("fn_subst", Hmtype.show_typ_env fn_subst)
     *   ; ("arg", string_of_expr arg)
     *   ; ("arg_subst", Hmtype.show_typ_env arg_subst)
     *   ]; *)
    ( match
        Hmtype.unify
          (Hmtype.replace_substitutions arg_subst fun_t)
          (TypeApp [ TypeConstant Arrow; arg_t; res_t ])
      with
    | Ok subst3 ->
      ( List.fold_left
          Hmtype.compose_substitutions
          subst3
          [ arg_subst; fn_subst ]
      , Hmtype.replace_substitutions subst3 res_t )
    | Error e ->
      failwith
        (Printf.sprintf
           "Wrong argument type given. Unification error: %s"
           (Hmtype.string_of_unify_err e) ) )
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
      | Error e ->
        failwith
          (Printf.sprintf
             "Let infer unification error: %s"
             (Hmtype.string_of_unify_err e) )
    else
      let s1, t1 = infer_type env value in
      let t' = Hmtype.generalize (Hmtype.replace_substitutions_env s1 env) t1 in
      let env' = (var, t') :: env in
      let s2, t2 = infer_type (Hmtype.replace_substitutions_env s1 env') body in
      (Hmtype.compose_substitutions s2 s1, t2)
  | Bool (_, _) -> (env, Hmtype.TypeConstant Hmtype.Boolean)
  | IfThenElse (_, Sym (_cond_pos, cond_s), then_e, else_e) ->
    let _then_subst, then_t = infer_type env then_e in
    let _else_subst, else_t = infer_type env else_e in
    (* Util.debugprint
     *   "IfThenElse infer"
     *   [ ("then_e", string_of_expr then_e)
     *   ; ("then_t", Hmtype.string_of_typ then_t)
     *   ; ("then_subst", Hmtype.show_typ_env then_subst)
     *   ; ("else_e", string_of_expr else_e)
     *   ; ("else_t", Hmtype.string_of_typ else_t)
     *   ; ("else_subst", Hmtype.show_typ_env else_subst)
     *   ]; *)
    ( match Hmtype.unify then_t else_t with
    | Error _unification_error -> failwith "Then and Else types mismatch"
    | Ok _then_else_unification_subst ->
      let cond_e : expr = Sym (_cond_pos, cond_s) in
      let _cond_subst, cond_t = infer_type env cond_e in
      ( match cond_t with
      | Hmtype.TypeVariable cond_t_s ->
        ((cond_t_s, Hmtype.TypeConstant Hmtype.Boolean) :: env, else_t)
      | _ -> failwith "Don't know what to do if If cond_t isn't a variable" ) )
  | IfThenElse (_, Bool _, then_e, else_e) ->
    let _then_subst, then_t = infer_type env then_e in
    let _else_subst, else_t = infer_type env else_e in
    (* Util.debugprint
     *   "IfThenElse infer"
     *   [ ("then_e", string_of_expr then_e)
     *   ; ("then_t", Hmtype.string_of_typ then_t)
     *   ; ("then_subst", Hmtype.show_typ_env then_subst)
     *   ; ("else_e", string_of_expr else_e)
     *   ; ("else_t", Hmtype.string_of_typ else_t)
     *   ; ("else_subst", Hmtype.show_typ_env else_subst)
     *   ]; *)
    ( match Hmtype.unify then_t else_t with
    | Error _e -> failwith "Unifying boolean ifelsethen value failure"
    | Ok _unification_subst -> (env, then_t) )
  | IfThenElse (_, _, _, _) -> failwith "not done yet ifthenelse"


let infer env (exp : expr) : Hmtype.typ =
  match Ok (infer_type env exp) with
  | Ok (substitutions, t) ->
    Hmtype.generalize env (Hmtype.replace_substitutions substitutions t)
  | _ -> failwith "infer_type error"
