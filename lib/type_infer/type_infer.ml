(* GREAT reading resources on type inferrence:
 * http://www.cs.tau.ac.il/~msagiv/courses/pl15/hindley_milner.change_to_py
 * https://github.com/rob-smallshire/hindley-milner-python/blob/master/inference.py
 * https://www.cs.cornell.edu/courses/cs3110/2011sp/Lectures/lec26-type-inference/type-inference.htm
 *)
let negpos = (-1, -1)

let rec pow a = function
  | 0 -> 1
  | 1 -> a
  | n ->
    let b = pow a (n / 2) in
    b * b * if n mod 2 = 0 then 1 else a


let rec zip xl yl =
  match (xl, yl) with
  | x :: xs, y :: ys -> (x, y) :: zip xs ys
  | [], [] -> []
  | _x :: _xs, []
  | [], _x :: _xs ->
    assert false


module UnifyContext = Map.Make (Type.Type)
module TVSet = Set.Make (Type.TypeVariable)

type position = int * int

exception UndefinedSymbolInTypeInferrer of position * string

exception TypeError of string

exception UnificationError of string

type typeof_error =
  | UndefinedSymbolInTypeInferrer of position * string (* WHY DOUBLE THIS? *)
  | TypeError of string
  | UnificationError of string

let rec typeof_exn
    (_gensym_state : Type.gensym_state)
    _expr
    (_context : (string * Type.Type.typ) list)
    (_non_generic : TVSet.t) : Type.Type.typ =
  failwith
    "match expr with\n\
    \  | Expr.Sym (pos, name) -> get_type pos gensym_state name context \
     non_generic\n\
    \  | App (pos, Sym (_, enum_symbol), Sym (_, tag_name))\n\
    \    when match List.assoc_opt enum_symbol context with\n\
    \         | Some (TyTagUnion (_, _cases)) -> true\n\
    \         | _ -> false ->\n\
    \    ( match List.assoc enum_symbol context with\n\
    \    | TyTagUnion (tyTagUnion_pos, cases) ->\n\
    \      typeof_exn\n\
    \        gensym_state\n\
    \        (App\n\
    \           (pos, Enum (TyTagUnion (tyTagUnion_pos, cases)), Sym (pos, \
     tag_name))\n\
    \        )\n\
    \        context\n\
    \        non_generic\n\
    \    | _ -> failwith \"zzzzzZZZzZ\" )\n\
    \  | App\n\
    \      (_, Enum (Type.Type.TyTagUnion (tyTagUnion_pos, cases)), Sym (_, \
     tag_name))\n\
    \    ->\n\
    \    ( match List.assoc_opt tag_name cases with\n\
    \    | Some tag_type ->\n\
    \      let return_value =\n\
    \        Type.tArrow tag_type (Type.Type.TyTagUnion (tyTagUnion_pos, cases))\n\
    \      in\n\
    \      return_value\n\
    \    | None ->\n\
    \      let _state, tytagunion_string =\n\
    \        Type.string_of_typ\n\
    \          (gensym_state.next_variable_id, gensym_state.next_variable_name)\n\
    \          (Type.Type.TyTagUnion (tyTagUnion_pos, cases))\n\
    \      in\n\
    \      failwith\n\
    \        (Printf.sprintf\n\
    \           \"TypeError!! tag %s not part of enum %s\"\n\
    \           tag_name\n\
    \           tytagunion_string ) )\n\
    \  | Expr.App (pos, fn, arg) ->\n\
    \    let fun_type = typeof_exn gensym_state fn context non_generic in\n\
    \    let arg_type = typeof_exn gensym_state arg context non_generic in\n\
    \    let state, result_type_param =\n\
    \      let state, tvar =\n\
    \        Type.typ_variable (Type.info_of_state gensym_state) \"\" None\n\
    \      in\n\
    \      Type.setstate gensym_state state;\n\
    \      (state, Type.Type.TyVar (pos, tvar))\n\
    \    in\n\
    \    Type.setstate gensym_state state;\n\
    \    unify gensym_state (Type.tArrow arg_type result_type_param) fun_type;\n\
    \    result_type_param\n\
    \  | Expr.Lam (_pos, []) -> failwith \"Can't type infer lambda without \
     args\"\n\
    \  | Expr.Lam (_pos, (PSym (_psym_pos, v), body) :: _rest) ->\n\
    \    let arg_type = Type.TypeVariable.create gensym_state in\n\
    \    let arg_type_param = Type.Type.TyVar (_psym_pos, arg_type) in\n\
    \    let new_context = (v, arg_type_param) :: context in\n\
    \    let new_non_generic = TVSet.add arg_type non_generic in\n\
    \    let result_type =\n\
    \      typeof_exn gensym_state body new_context new_non_generic\n\
    \    in\n\
    \    Type.tArrow arg_type_param result_type\n\
    \  | Expr.Lam (_, (PTag (_, _, _), _) :: _) ->\n\
    \    failwith \"TODO can't yet type check functions of patterns\"\n\
    \  (* In the future, a macro may convert the body of the following \
     expression\n\
    \     from: `(let Bool (enum True False) True)` into: `(let Bool (enum True\n\
    \     False) (Bool True <>))`. The reason to prefer the latter as \
     canonical is to\n\
    \     be obvious about when things are defined - what if the enum is the \
     result\n\
    \     of a function call? *)\n\
    \  | Expr.Let (_pos, name, defn, body) ->\n\
    \    let defn_type = typeof_exn gensym_state defn context non_generic in\n\
    \    let new_context = (name, defn_type) :: context in\n\
    \    typeof_exn gensym_state body new_context non_generic\n\
    \  | Expr.Letrec (pos, name, defn, body) ->\n\
    \    let new_type = Type.TypeVariable.create gensym_state in\n\
    \    let new_type_param = Type.Type.TyVar (pos, new_type) in\n\
    \    let new_context = (name, new_type_param) :: context in\n\
    \    let new_non_generic = TVSet.add new_type non_generic in\n\
    \    let defn_type = typeof_exn gensym_state defn new_context \
     new_non_generic in\n\
    \    unify gensym_state new_type_param defn_type;\n\
    \    typeof_exn gensym_state body new_context non_generic\n\
    \  | Expr.Unit _pos -> Type.tUnit\n\
    \  | Expr.U8 (_n, _pos) -> Type.tU8\n\
    \  | Expr.Ann (_pos, expected_typ, given_expr) ->\n\
    \    let given_expr_type =\n\
    \      typeof_exn gensym_state given_expr context non_generic\n\
    \    in\n\
    \    unify gensym_state expected_typ given_expr_type;\n\
    \    given_expr_type\n\
    \  | Expr.String (_pos, _s) -> Type.tString\n\
    \  (* | Expr.None _pos -> tUnit *)\n\
    \  | Expr.Vector (pos, xs) ->\n\
    \    let new_type = Type.TypeVariable.create gensym_state in\n\
    \    let new_type_param = Type.Type.TyVar (pos, new_type) in\n\
    \    let xs_types =\n\
    \      List.map (fun expr -> typeof_exn gensym_state expr context \
     non_generic) xs\n\
    \    in\n\
    \    List.iter (fun ty -> unify gensym_state new_type_param ty) xs_types;\n\
    \    Type.tVector new_type_param\n\
    \  | Expr.Dict (pos, key_value_pairs) ->\n\
    \    let unify_many (xs : Expr.expr list) : Type.Type.typ =\n\
    \      let new_type = Type.TypeVariable.create gensym_state in\n\
    \      let new_type_param = Type.Type.TyVar (pos, new_type) in\n\
    \      let xs_types =\n\
    \        List.map\n\
    \          (fun expr -> typeof_exn gensym_state expr context non_generic)\n\
    \          xs\n\
    \      in\n\
    \      List.iter (fun ty -> unify gensym_state new_type_param ty) xs_types;\n\
    \      new_type_param\n\
    \    in\n\
    \    let keys, values =\n\
    \      (List.map fst key_value_pairs, List.map snd key_value_pairs)\n\
    \    in\n\
    \    Type.tDict (unify_many keys) (unify_many values)\n\
    \  | Match (_pos, _x, []) -> failwith \"Match with no cases makes no sense\"\n\
    \  | Match (pos, x, cases) ->\n\
    \    let new_type = Type.TypeVariable.create gensym_state in\n\
    \    let new_type_param = Type.Type.TyVar (pos, new_type) in\n\
    \    (* (match x\n\
    \              y y\n\
    \              z z)\n\
    \     * Return type is type of `((λ y y) x)` and `((λ z z) x)` given they \
     are equal *)\n\
    \    let appize x case = Expr.App ((-1, -1), Expr.Lam ((-1, -1), [ case \
     ]), x) in\n\
    \    let cases_appized_types =\n\
    \      cases\n\
    \      |> List.map (appize x)\n\
    \      |> List.map (fun expr ->\n\
    \             typeof_exn gensym_state expr context non_generic )\n\
    \    in\n\
    \    List.iter\n\
    \      (fun ty -> unify gensym_state new_type_param ty)\n\
    \      cases_appized_types;\n\
    \    new_type_param\n\
    \  | Tuple (_, _)\n\
    \  | Set (_, _) ->\n\
    \    failwith \"TODO `typeof_exn` of Tuple not yet implemented\"\n\
    \  | TaggedValue (tag, TyTagUnion (_TyTagUnion_pos, cases), value) ->\n\
    \    ( match List.assoc_opt tag cases with\n\
    \    | Some t when typeof_exn gensym_state value context non_generic = t ->\n\
    \      TyTagUnion (_TyTagUnion_pos, cases)\n\
    \    | Some _t ->\n\
    \      failwith (Printf.sprintf \"Tag %s given wrong type for Enum\" tag)\n\
    \    | None -> failwith (Printf.sprintf \"Tag %s not found in Enum\" tag) )\n\
    \  | TaggedValue (_name, TyVar (_, tvar), _value) ->\n\
    \    typeof_exn\n\
    \      gensym_state\n\
    \      (TaggedValue (_name, List.assoc tvar.name context, _value))\n\
    \      context\n\
    \      non_generic\n\
    \  | TaggedValue (name, _enum, _value) ->\n\
    \    failwith\n\
    \      (Printf.sprintf\n\
    \         \"TypeError: Given TaggedValue where enum is neither TyEnum nor \
     TyVar. \\\n\
    \          name = %s\"\n\
    \         name )\n\
    \  | Enum t -> t\n\
    \  | TypeDef (pos, args, child_expr) ->\n\
    \    Printf.printf \"Got into TypeDef\\n\";\n\
    \    ( match List.nth_opt args 0 with\n\
    \    | Some first_arg ->\n\
    \      Type.Type.TyForall\n\
    \        (pos, first_arg, typeof_exn gensym_state child_expr context \
     non_generic)\n\
    \    | None -> typeof_exn gensym_state child_expr context non_generic )\n"


and typeof_pure state expr context non_generic :
    (Type.gensym_info * Type.Type.typ, typeof_error) result =
  match expr with
  | Expr.Sym (pos, name) -> get_type_pure state pos name context non_generic
  | Expr.App (pos, fn, arg) ->
    let string_of_typeof_error = function
      | UnificationError e -> "UnificationError: " ^ e
      | TypeError e -> "TypeError: " ^ e
      | UndefinedSymbolInTypeInferrer (_pos, e) ->
        "UndefinedSymbolInTypeInferrer: " ^ e
    in

    let state, fun_type =
      State.unwrap
        string_of_typeof_error
        (typeof_pure state fn context non_generic)
    in
    let state, arg_type =
      State.unwrap
        string_of_typeof_error
        (typeof_pure state arg context non_generic)
    in
    let state, result_type_param =
      let state, tvar = Type.typ_variable state "" None in
      (state, Type.Type.TyVar (pos, tvar))
    in
    ( match
        unify_pure state (Type.tArrow arg_type result_type_param) fun_type
      with
    | Ok (state, tvar, _fun_type) -> Ok (state, tvar)
    | Error _e -> failwith "shiiiiiittttt yo " )
  | _ ->
    let _state, expr_string = Expr.string_of_expr state expr in
    Error (TypeError ("whoops not done: " ^ expr_string))
(* and typeof_pure
 *     (state : Type.gensym_info)
 *     expr
 *     (context : (string * Type.Type.typ) list)
 *     (non_generic : TVSet.t) : Type.gensym_info * Type.Type.typ =
 *   match expr with
 *   | Expr.Sym (pos, name) -> get_type_pure state pos name context non_generic
 *   | App (pos, Sym (_, enum_symbol), Sym (_, tag_name))
 *     when match List.assoc_opt enum_symbol context with
 *          | Some (TyTagUnion (_, _cases)) -> true
 *          | _ -> false ->
 *     ( match List.assoc enum_symbol context with
 *     | TyTagUnion (tyTagUnion_pos, cases) ->
 *       typeof_pure
 *         state
 *         (App
 *            (pos, Enum (TyTagUnion (tyTagUnion_pos, cases)), Sym (pos, tag_name))
 *         )
 *         context
 *         non_generic
 *     | _ -> failwith "zzzzzZZZzZ" )
 *   | App
 *       (_, Enum (Type.Type.TyTagUnion (tyTagUnion_pos, cases)), Sym (_, tag_name))
 *     ->
 *     ( match List.assoc_opt tag_name cases with
 *     | Some tag_type ->
 *       let return_value =
 *         Type.tArrow tag_type (Type.Type.TyTagUnion (tyTagUnion_pos, cases))
 *       in
 *       (state, return_value)
 *     | None ->
 *       let state, tytagunion_string =
 *         Type.string_of_typ state (Type.Type.TyTagUnion (tyTagUnion_pos, cases))
 *       in
 *       failwith
 *         (Printf.sprintf
 *            "TypeError!! tag %s not part of enum %s"
 *            tag_name
 *            tytagunion_string ) )
 *   | Expr.App (pos, fn, arg) ->
 *     let state, fun_type = typeof_pure state fn context non_generic in
 *     let state, arg_type = typeof_pure state arg context non_generic in
 *     let state, result_type_param =
 *       let state, tvar = Type.create_typ_variable state "" in
 *       (state, Type.Type.TyVar (pos, tvar))
 *     in
 *     unify_pure gensym_state (Type.tArrow arg_type result_type_param) fun_type;
 *     result_type_param
 *   | Expr.Lam (_pos, []) -> failwith "Can't type infer lambda without args"
 *   | Expr.Lam (_pos, (PSym (_psym_pos, v), body) :: _rest) ->
 *     let arg_type = Type.TypeVariable.create gensym_state in
 *     let arg_type_param = Type.Type.TyVar (_psym_pos, arg_type) in
 *     let new_context = (v, arg_type_param) :: context in
 *     let new_non_generic = TVSet.add arg_type non_generic in
 *     let result_type =
 *       typeof_exn gensym_state body new_context new_non_generic
 *     in
 *     Type.tArrow arg_type_param result_type
 *   | Expr.Lam (_, (PTag (_, _, _), _) :: _) ->
 *     failwith "TODO can't yet type check functions of patterns"
 *   (\* In the future, a macro may convert the body of the following expression
 *      from: `(let Bool (enum True False) True)` into: `(let Bool (enum True
 *      False) (Bool True <>))`. The reason to prefer the latter as canonical is to
 *      be obvious about when things are defined - what if the enum is the result
 *      of a function call? *\)
 *   | Expr.Let (_pos, name, defn, body) ->
 *     let defn_type = typeof_exn gensym_state defn context non_generic in
 *     let new_context = (name, defn_type) :: context in
 *     typeof_exn gensym_state body new_context non_generic
 *   | Expr.Letrec (pos, name, defn, body) ->
 *     let new_type = Type.TypeVariable.create gensym_state in
 *     let new_type_param = Type.Type.TyVar (pos, new_type) in
 *     let new_context = (name, new_type_param) :: context in
 *     let new_non_generic = TVSet.add new_type non_generic in
 *     let defn_type = typeof_exn gensym_state defn new_context new_non_generic in
 *     unify gensym_state new_type_param defn_type;
 *     typeof_exn gensym_state body new_context non_generic
 *   | Expr.Unit _pos -> Type.tUnit
 *   | Expr.U8 (_n, _pos) -> Type.tU8
 *   | Expr.Ann (_pos, expected_typ, given_expr) ->
 *     let given_expr_type =
 *       typeof_exn gensym_state given_expr context non_generic
 *     in
 *     unify gensym_state expected_typ given_expr_type;
 *     given_expr_type
 *   | Expr.String (_pos, _s) -> Type.tString
 *   (\* | Expr.None _pos -> tUnit *\)
 *   | Expr.Vector (pos, xs) ->
 *     let new_type = Type.TypeVariable.create gensym_state in
 *     let new_type_param = Type.Type.TyVar (pos, new_type) in
 *     let xs_types =
 *       List.map (fun expr -> typeof_exn gensym_state expr context non_generic) xs
 *     in
 *     List.iter (fun ty -> unify gensym_state new_type_param ty) xs_types;
 *     Type.tVector new_type_param
 *   | Expr.Dict (pos, key_value_pairs) ->
 *     let keys = List.map fst key_value_pairs in
 *     let values = List.map snd key_value_pairs in
 *     let unify_many (xs : Expr.expr list) : Type.Type.typ =
 *       let new_type = Type.TypeVariable.create gensym_state in
 *       let new_type_param = Type.Type.TyVar (pos, new_type) in
 *       let xs_types =
 *         List.map
 *           (fun expr -> typeof_exn gensym_state expr context non_generic)
 *           xs
 *       in
 *       List.iter (fun ty -> unify gensym_state new_type_param ty) xs_types;
 *       new_type_param
 *     in
 *     Type.tDict (unify_many keys) (unify_many values)
 *   | Match (_pos, _x, []) -> failwith "Match with no cases makes no sense"
 *   | Match (pos, x, cases) ->
 *     let new_type = Type.TypeVariable.create gensym_state in
 *     let new_type_param = Type.Type.TyVar (pos, new_type) in
 *     (\* (match x
 *               y y
 *               z z)
 *      * Return type is type of `((λ y y) x)` and `((λ z z) x)` given they are equal *\)
 *     let appize x case = Expr.App ((-1, -1), Expr.Lam ((-1, -1), [ case ]), x) in
 *     let cases_appized_types =
 *       cases
 *       |> List.map (appize x)
 *       |> List.map (fun expr ->
 *              typeof_exn gensym_state expr context non_generic )
 *     in
 *     List.iter
 *       (fun ty -> unify gensym_state new_type_param ty)
 *       cases_appized_types;
 *     new_type_param
 *   | Tuple (_, _)
 *   | Set (_, _) ->
 *     failwith "TODO `typeof_exn` of Tuple not yet implemented"
 *   | TaggedValue (tag, TyTagUnion (_TyTagUnion_pos, cases), value) ->
 *     ( match List.assoc_opt tag cases with
 *     | Some t when typeof_exn gensym_state value context non_generic = t ->
 *       TyTagUnion (_TyTagUnion_pos, cases)
 *     | Some _t ->
 *       failwith (Printf.sprintf "Tag %s given wrong type for Enum" tag)
 *     | None -> failwith (Printf.sprintf "Tag %s not found in Enum" tag) )
 *   | TaggedValue (_name, TyVar (_, tvar), _value) ->
 *     typeof_exn
 *       gensym_state
 *       (TaggedValue (_name, List.assoc tvar.name context, _value))
 *       context
 *       non_generic
 *   | TaggedValue (name, _enum, _value) ->
 *     failwith
 *       (Printf.sprintf
 *          "TypeError: Given TaggedValue where enum is neither TyEnum nor TyVar. \
 *           name = %s"
 *          name )
 *   | Enum t -> t
 *   | TypeDef (pos, args, child_expr) ->
 *     Printf.printf "Got into TypeDef\n";
 *     ( match List.nth_opt args 0 with
 *     | Some first_arg ->
 *       Type.Type.TyForall
 *         (pos, first_arg, typeof_exn gensym_state child_expr context non_generic)
 *     | None -> typeof_exn gensym_state child_expr context non_generic ) *)


and string_of_context state =
  let rec inner state acc = function
    | (name, typ) :: rest ->
      let state, typ_string = Type.string_of_typ state typ in
      inner state ("(" ^ name ^ " " ^ typ_string ^ ")") rest
    | [] -> (state, acc ^ ")")
  in
  inner state "("


and get_type pos gensym_state name context non_generic =
  if List.mem_assoc name context
  then fresh gensym_state (List.assoc name context) non_generic
  else raise (UndefinedSymbolInTypeInferrer (pos, name))


and get_type_pure state pos name context non_generic =
  if List.mem_assoc name context
  then Ok (fresh_pure state (List.assoc name context) non_generic)
  else Error (UndefinedSymbolInTypeInferrer (pos, name))


(* Get a fresh type *)
and fresh gensym_state (t : Type.Type.typ) (non_generic : TVSet.t) :
    Type.Type.typ =
  let mappings = Hashtbl.create 30 in
  let rec inner (typ : Type.Type.typ) : Type.Type.typ =
    let pruned_typ = prune typ in
    match pruned_typ with
    | Type.Type.TyVar (tyVar_pos, tv) ->
      let non_generic_list =
        List.map
          (fun a -> Type.Type.TyVar (tyVar_pos, a))
          (TVSet.elements non_generic)
      in
      if is_generic tv non_generic_list
      then (
        if not (Hashtbl.mem mappings pruned_typ)
        then
          Hashtbl.replace
            mappings
            pruned_typ
            (Type.Type.TyVar (tyVar_pos, Type.TypeVariable.create gensym_state));
        Hashtbl.find mappings pruned_typ )
      else pruned_typ
    | Type.Type.TyTag (tyTag_post, name, child_type) ->
      Type.Type.TyTag (tyTag_post, name, inner child_type)
    | Type.Type.TyTagUnion (tyTagUnion_pos, child_types) ->
      Type.Type.TyTagUnion
        (tyTagUnion_pos, List.map (fun (name, x) -> (name, inner x)) child_types)
    | Type.Type.TyOp (pos, name, child_types) ->
      Type.Type.TyOp (pos, name, List.map (fun x -> inner x) child_types)
    | Type.Type.TyForall (pos, name, child_type) ->
      Type.Type.TyForall (pos, name, inner child_type)
    | TyApp (_pos, _f, _x) -> pruned_typ
  in

  (* debug *)
  let result = inner t in
  let state = Type.info_of_state gensym_state in
  let state, typ_string = Type.string_of_typ state t in
  let (non_generic_list : Type.TypeVariable.t list) =
    TVSet.elements non_generic
  in
  let state, non_generic_strings =
    State.map
      (fun state (typvar : Type.TypeVariable.t) ->
        Type.string_of_typ_variable state typvar.instance typvar.name )
      []
      state
      non_generic_list
  in
  let state, result_string = Type.string_of_typ state result in
  Printf.printf
    "fresh_pure result: %s, state: %s t: %s non_generic: %s"
    result_string
    (Type.string_of_info state)
    typ_string
    (String.concat ", " non_generic_strings);

  inner t


and fresh_pure
    (state : Type.gensym_info) (t : Type.Type.typ) (non_generic : TVSet.t) :
    Type.gensym_info * Type.Type.typ =
  let mappings = Hashtbl.create 30 in
  let rec inner state (typ : Type.Type.typ) : Type.gensym_info * Type.Type.typ =
    let pruned_typ = prune typ in
    match pruned_typ with
    | Type.Type.TyVar (tyVar_pos, tv) ->
      let non_generic_list =
        List.map
          (fun a -> Type.Type.TyVar (tyVar_pos, a))
          (TVSet.elements non_generic)
      in
      let state, tvar = Type.typ_variable state "" None in
      if is_generic tv non_generic_list
      then (
        if not (Hashtbl.mem mappings pruned_typ)
        then
          Hashtbl.replace mappings pruned_typ (Type.Type.TyVar (tyVar_pos, tvar));
        (state, Hashtbl.find mappings pruned_typ) )
      else (state, pruned_typ)
    | Type.Type.TyTag (tyTag_post, name, child_type) ->
      let state, inner_of_children = inner state child_type in
      (state, Type.Type.TyTag (tyTag_post, name, inner_of_children))
    | Type.Type.TyTagUnion (tyTagUnion_pos, child_types) ->
      let state, refreshed_children =
        State.map
          (fun state (name, x) ->
            let state, x = inner state x in
            (state, (name, x)) )
          []
          state
          child_types
      in
      (state, Type.Type.TyTagUnion (tyTagUnion_pos, refreshed_children))
    | Type.Type.TyOp (pos, name, child_types) ->
      let state, refreshed_children =
        State.map (fun state x -> inner state x) [] state child_types
      in
      (state, Type.Type.TyOp (pos, name, refreshed_children))
    | Type.Type.TyForall (pos, name, child_type) ->
      let state, refreshed_child = inner state child_type in
      (state, Type.Type.TyForall (pos, name, refreshed_child))
    | TyApp (_pos, _f, _x) -> (state, pruned_typ)
  in
  let state, result = inner state t in
  let state, typ_string = Type.string_of_typ state t in
  let (non_generic_list : Type.TypeVariable.t list) =
    TVSet.elements non_generic
  in
  let state, non_generic_strings =
    State.map
      (fun state (typvar : Type.TypeVariable.t) ->
        Type.string_of_typ_variable state typvar.instance typvar.name )
      []
      state
      non_generic_list
  in
  let state, result_string = Type.string_of_typ state result in
  Printf.printf
    "fresh_pure result: %s, state: %s t: %s non_generic: %s"
    result_string
    (Type.string_of_info state)
    typ_string
    (String.concat ", " non_generic_strings);
  (state, result)
(* Har igång type inferrence som kan göra letrec nu, Hindley Milner.
 *
 * Tänker på unification - man har ju två varianter av expr, Term och Symbol, där Term har ett namn och en lista med expressions.
 *
 * Med det kan man implementera OCH-relationer, alltså att "->" har två variablar "a" och "b". Den är alltså "forall", och implementerar "och"-relationen.
 *
 * "Eller" eller "or"-relationen är ännu inte implementerad, som i hur en (Maybe a) är en (Just a) eller None. Tänker att man behöver en ny variant på expr förutom "Term", som istället kunde heta "OrTerm" eller så. En `| OrTerm of string * expr list`. Så när unify finner ut typen av en variabel, och den variabeln i evaluation context pekar på en OrTerm, *)


(* Unify the two types t1 and t2 Makes the types t1 and t2 the same *)
and unify gensym_state t1 t2 : unit =
  let a = prune t1 in
  let b = prune t2 in
  (* let printf_gensym_state = Type.new_gensym_state () in
   * Printf.printf
   *   "unify: a=%s b=%s"
   *   (snd (Type.string_of_typ (Type.info_of_state printf_gensym_state) t1))
   *   (snd (Type.string_of_typ (Type.info_of_state printf_gensym_state) t2)); *)
  match (a, b) with
  | Type.Type.TyVar (_pos, tyvar), _ ->
    if a <> b
    then
      if occurs_in_type tyvar b
      then raise (TypeError "recursive unification")
      else tyvar.Type.TypeVariable.instance <- Some b
    else failwith "in that weird unify branch"
  | _ (* Type.Type.TyOp(_top) *), Type.Type.TyVar (_pos, _tyvar) ->
    unify gensym_state b a
  (* | (Type.Type.TyOp (top1_name, top1_types), Type.Type.TyTag (tytag_name,
     tytag_type)) -> *)
  (* (let Maybe (enum (Maybe a) (Just a) None) (Maybe Just (u8 1))) TyEnum
     ("Maybe", ty_var "a", [Ty]) *)
  | ( Type.Type.TyOp (tyOp1_pos, top1_name, top1_types)
    , Type.Type.TyOp (tyOp2_pos, top2_name, top2_types) ) ->
    (* Same names and arity *)
    let top1_types_size = List.length top1_types in
    let top2_types_size = List.length top2_types in
    (* JESPER! Här kollar vi att båda Terms eller Type Operators (TyOp) har
       samma namn och antal argument *)
    (* Med OR type operators aka terms, så måste vi istället kolla om den ena
       eller andra TypeOperator har label som en "child" av den andra. Detta för
       att "(Just a)" inte är = (Maybe a), men matchar child of (Maybe a). *)
    if top1_name <> top2_name || top1_types_size <> top2_types_size
    then
      raise
        (TypeError
           ( "Type mismatch "
           ^ snd
               (Type.string_of_typ
                  (Type.info_of_state gensym_state)
                  (TyOp (tyOp1_pos, top1_name, top1_types)) )
           ^ " != "
           ^ snd
               (Type.string_of_typ
                  (Type.info_of_state gensym_state)
                  (TyOp (tyOp2_pos, top2_name, top2_types)) ) ) );
    (* Här kollar den bara om TypeOperators top1 och top2 är lika - men med OR
       behöver den också kolla om den ena är "child" till den andra, vilket är
       enkelt som att kolla om List.contains i den ena eller andras children.
       Kom ihåg, en typ = Sym of string | TypeOperator of string * typ list |
       TypeOperatorOr of string * typ list.

       Så (Maybe a) => (TypeOperatorOr "Maybe" [Sym "a"]) Och (Just a) =>
       (TypeOperator "Just" [Sym "a"]) unify (Maybe a) (Just b) => (Maybe a)*)
    List.iter2 (unify gensym_state) top1_types top2_types
  | ( Type.Type.TyTagUnion (tyTagUnion_pos, cases)
    , Type.Type.TyTag (_tyTag_pos, tag_name, tag_typ) )
  | ( Type.Type.TyTag (_tyTag_pos, tag_name, tag_typ)
    , Type.Type.TyTagUnion (tyTagUnion_pos, cases) ) ->
    ( match List.assoc_opt tag_name cases with
    | Some canonical_typ ->
      (* canonical type is what we expect - it should unify with tag_type *)
      unify gensym_state canonical_typ tag_typ
    | None ->
      raise
        (TypeError
           ( "Union Tag mismatch "
           ^ snd
               (Type.string_of_typ
                  (Type.info_of_state gensym_state)
                  (Type.Type.TyTagUnion (tyTagUnion_pos, cases)) )
           ^ "not matching "
           ^ snd (Type.string_of_typ (Type.info_of_state gensym_state) tag_typ)
           ) ) )
  | Type.Type.TyOp (_, _, _), (Type.Type.TyTag _ | TyTagUnion _)
  | (TyTag _ | TyTagUnion _), TyOp (_, _, _) ->
    raise
      (TypeError
         (Printf.sprintf
            "TyOp and TyTag|TyTagUnion don't unify. \na: %s\nb: %s"
            (snd (Type.string_of_typ (Type.info_of_state gensym_state) a))
            (snd (Type.string_of_typ (Type.info_of_state gensym_state) b)) ) )
  | Type.Type.TyTag (_, t1_name, t1_typ), Type.Type.TyTag (_, t2_name, t2_typ)
    ->
    if t1_name = t2_name
    then unify gensym_state t1_typ t2_typ
    else
      raise (TypeError "Given two TyTag but they are not of the same tag name")
  | TyTagUnion _, TyTagUnion _ -> unify gensym_state a b
  | TyOp (_, _, _), TyForall (_, _, _) -> failwith "TODO think about this"
  | _ -> failwith "FIX THIS"


(* Returns the currently defining instance of t.

   As a side effect, collapses the list of type instances. The function Prune is
   used whenever a type expression has to be inspected: it will always return a
   type expression which is either an uninstantiated type variable or a type
   operator; i.e. it will skip instantiated variables, and will actually prune
   them from expressions to remove long chains of instantiated variables.

   Args: t: The type to be pruned

   Returns: An uninstantiated TypeVariable or a TypeOperator *)
and prune (t : Type.Type.typ) =
  Printf.printf "stateful prune\n";
  match t with
  | Type.Type.TyVar (_tv_pos, tv) ->
    ( match tv.Type.TypeVariable.instance with
    | Some stv ->
      tv.Type.TypeVariable.instance <- Some (prune stv);
      stv
    | None -> t )
  | _ -> t


(* Returns the tuple of new_state, the new instance of t if it's a TypeVariable,
   and at last t pruned *)
and prune_pure state typ =
  match typ with
  | Type.Type.TyVar (pos, tv) ->
    ( match tv.Type.TypeVariable.instance with
    | Some typ ->
      let state, prune_pure_result = prune_pure state typ in
      let state, typ =
        Type.typ_variable
          state
          tv.Type.TypeVariable.name
          (Some prune_pure_result)
      in
      (state, Type.Type.TyVar (pos, typ))
    | None -> (state, typ) )
  | _ -> (state, typ)


and is_generic (v : Type.TypeVariable.t) non_generic =
  not (occurs_in v non_generic)


and occurs_in_type (v : Type.TypeVariable.t) t2 =
  let pruned_t2 = prune t2 in
  match pruned_t2 with
  | Type.Type.TyVar (_tv_pos, tv) when tv = v -> true
  | Type.Type.TyOp (_tyOp1_pos, _name, tyop_types) -> occurs_in v tyop_types
  | _ -> false


and occurs_in_type_pure state v t2 =
  match prune_pure state t2 with
  | state, Type.Type.TyVar (_tv_pos, tv) when tv = v -> (state, true)
  | state, Type.Type.TyOp (_tyop_pos, _name, tyop_types) ->
    occurs_in_pure state v tyop_types
  | _ -> (state, false)


and occurs_in (t : Type.TypeVariable.t) (types : Type.Type.typ list) =
  List.exists (fun t2 -> occurs_in_type t t2) types


and occurs_in_pure state (t : Type.TypeVariable.t) (types : Type.Type.typ list)
    : Type.gensym_info * bool =
  State.exists
    (fun state (t2 : Type.Type.typ) -> occurs_in_type_pure state t t2)
    state
    types


and is_integer_literal name =
  try
    ignore (int_of_string name);
    true
  with
  | Failure _ -> false


and unify_pure
    (_state : Type.gensym_info) (_t1 : Type.Type.typ) (_t2 : Type.Type.typ) :
    (Type.gensym_info * Type.Type.typ * Type.Type.typ, typeof_error) result =
  failwith
    "let state, t1 = prune_pure state t1 in\n\
    \  let state, t2 = prune_pure state t2 in\n\
    \  (* let printf_gensym_state = Type.new_gensym_state () in\n\
    \   * Printf.printf\n\
    \   *   \"unify: a=%s b=%s\"\n\
    \   *   (snd (Type.string_of_typ (Type.info_of_state printf_gensym_state) \
     t1))\n\
    \   *   (snd (Type.string_of_typ (Type.info_of_state printf_gensym_state) \
     t2)); *)\n\
    \  match (t1, t2) with\n\
    \  | Type.Type.TyVar (pos, tyvar), _ ->\n\
    \    if t1 <> t2\n\
    \    then\n\
    \      let state, is_occurring = occurs_in_type_pure state tyvar t2 in\n\
    \      if is_occurring\n\
    \      then Error (TypeError \"recursive unification\")\n\
    \      else\n\
    \        let state, t2_tvar =\n\
    \          Type.typ_variable state tyvar.Type.TypeVariable.name (Some t2)\n\
    \        in\n\
    \        (* TODO check the logic here *)\n\
    \        Ok (state, t1, Type.Type.TyVar (pos, t2_tvar))\n\
    \    else failwith \"in that weird unify branch\"\n\
    \  | _ (* Type.Type.TyOp(_top) *), Type.Type.TyVar (_pos, _tyvar) ->\n\
    \    unify_pure state t2 t1\n\
    \  (* | (Type.Type.TyOp (top1_name, top1_types), Type.Type.TyTag \
     (tytag_name,\n\
    \     tytag_type)) -> *)\n\
    \  (* (let Maybe (enum (Maybe a) (Just a) None) (Maybe Just (u8 1))) TyEnum\n\
    \     (\"Maybe\", ty_var \"a\", [Ty]) *)\n\
    \  | ( Type.Type.TyOp (tyOp1_pos, top1_name, top1_types)\n\
    \    , Type.Type.TyOp (tyOp2_pos, top2_name, top2_types) ) ->\n\
    \    (* Same names and arity *)\n\
    \    let top1_types_size = List.length top1_types in\n\
    \    let top2_types_size = List.length top2_types in\n\
    \    (* JESPER! Här kollar vi att båda Terms eller Type Operators (TyOp) har\n\
    \       samma namn och antal argument *)\n\
    \    (* Med OR type operators aka terms, så måste vi istället kolla om den \
     ena\n\
    \       eller andra TypeOperator har label som en \"child\" av den andra. \
     Detta för\n\
    \       att \"(Just a)\" inte är = (Maybe a), men matchar child of (Maybe \
     a). *)\n\
    \    if top1_name <> top2_name || top1_types_size <> top2_types_size\n\
    \    then\n\
    \      raise\n\
    \        (TypeError\n\
    \           ( \"Type mismatch \"\n\
    \           ^ snd\n\
    \               (Type.string_of_typ\n\
    \                  state\n\
    \                  (TyOp (tyOp1_pos, top1_name, top1_types)) )\n\
    \           ^ \" != \"\n\
    \           ^ snd\n\
    \               (Type.string_of_typ\n\
    \                  state\n\
    \                  (TyOp (tyOp2_pos, top2_name, top2_types)) ) ) )\n\
    \      (* Här kollar den bara om TypeOperators top1 och top2 är lika - men \
     med OR\n\
    \         behöver den också kolla om den ena är \"child\" till den andra, \
     vilket är\n\
    \         enkelt som att kolla om List.contains i den ena eller andras \
     children.\n\
    \         Kom ihåg, en typ = Sym of string | TypeOperator of string * typ \
     list |\n\
    \         TypeOperatorOr of string * typ list.\n\n\
    \         Så (Maybe a) => (TypeOperatorOr \"\n\
    \    Maybe\n\
    \    \" [Sym \"\n\
    \    a\n\
    \    \"]) Och (Just a) =>\n\
    \         (TypeOperator \"\n\
    \    Just\n\
    \    \" [Sym \"\n\
    \    a\n\
    \    \"]) unify (Maybe a) (Just b) => (Maybe a)*)\n\
    \      (* Recursively apply `unify_pure state` to all items in \
     `top1_types` and\n\
    \         `top2_types` *)\n\
    \    else\n\
    \      let rec recur f state acc top1_types top2_types =\n\
    \        match (top1_types, top2_types) with\n\
    \        | [], [] -> acc\n\
    \        | t1 :: top1_types, t2 :: top2_types ->\n\
    \          let state, result = f state t1 t2 in\n\
    \          recur f state ((t1, t2) :: acc) top1_types top2_types\n\
    \      in\n\
    \      recur f state [] top1_types top2_types\n\
    \    (* else List.iter2 (unify_pure state) top1_types top2_types *)\n\
    \  | ( Type.Type.TyTagUnion (tyTagUnion_pos, cases)\n\
    \    , Type.Type.TyTag (_tyTag_pos, tag_name, tag_typ) )\n\
    \  | ( Type.Type.TyTag (_tyTag_pos, tag_name, tag_typ)\n\
    \    , Type.Type.TyTagUnion (tyTagUnion_pos, cases) ) ->\n\
    \    ( match List.assoc_opt tag_name cases with\n\
    \    | Some canonical_typ ->\n\
    \      (* canonical type is what we expect - it should unify with tag_type \
     *)\n\
    \      unify gensym_state canonical_typ tag_typ\n\
    \    | None ->\n\
    \      raise\n\
    \        (TypeError\n\
    \           ( \"\n\
    \    Union\n\
    \    Tag\n\
    \    mismatch\n\
    \    \"\n\
    \           ^ snd\n\
    \               (Type.string_of_typ\n\
    \                  (Type.info_of_state gensym_state)\n\
    \                  (Type.Type.TyTagUnion (tyTagUnion_pos, cases)) )\n\
    \           ^ \"\n\
    \    not\n\
    \    matching\n\
    \    \"\n\
    \           ^ snd (Type.string_of_typ (Type.info_of_state gensym_state) \
     tag_typ)\n\
    \           ) ) )\n\
    \  | Type.Type.TyOp (_, _, _), (Type.Type.TyTag _ | TyTagUnion _)\n\
    \  | (TyTag _ | TyTagUnion _), TyOp (_, _, _) ->\n\
    \    raise\n\
    \      (TypeError\n\
    \         (Printf.sprintf\n\
    \            \"TyOp and TyTag|TyTagUnion don't unify. \n\
     a: %s\n\
     b: %s\"\n\
    \            (snd (Type.string_of_typ (Type.info_of_state gensym_state) a))\n\
    \            (snd (Type.string_of_typ (Type.info_of_state gensym_state) \
     b)) ) )\n\
    \  | Type.Type.TyTag (_, t1_name, t1_typ), Type.Type.TyTag (_, t2_name, \
     t2_typ)\n\
    \    ->\n\
    \    if t1_name = t2_name\n\
    \    then unify gensym_state t1_typ t2_typ\n\
    \    else\n\
    \      raise (TypeError \"Given two TyTag but they are not of the same tag \
     name\")\n\
    \  | TyTagUnion _, TyTagUnion _ -> unify gensym_state a b\n\
    \  | TyOp (_, _, _), TyForall (_, _, _) -> failwith \"TODO think about \
     this\"\n\
    \  | _ -> failwith \"FIX THIS\"\n"


let fresh_tests =
  [ ( "old fresh returns expected value"
    , let gensym_state = Type.new_gensym_state () in
      let _ =
        let state, tvar = Type.tVar_pure (Type.info_of_state gensym_state) in
        Type.setstate gensym_state state;
        fresh gensym_state tvar TVSet.empty
      in
      let state, tyvar = Type.tVar_pure (Type.info_of_state gensym_state) in
      Type.setstate gensym_state state;
      fresh gensym_state tyvar TVSet.empty
      = Type.Type.TyVar
          ((-1, -1), { Type.TypeVariable.id = 3; name = ""; instance = None })
    )
  ; ( "fresh new"
    , let state = (0, 'a') in
      let state, tvar = Type.tVar_pure state in
      fresh_pure state tvar TVSet.empty
      = ( (2, 'a')
        , Type.Type.TyVar
            ((-1, -1), { Type.TypeVariable.id = 3; name = ""; instance = None })
        ) )
  ]


let try_exp (gensym_state : Type.gensym_state) context expr =
  Printf.printf
    "%s: "
    (snd (Expr.string_of_expr (Type.info_of_state gensym_state) expr));
  try
    print_endline
      (snd
         (Type.string_of_typ
            (Type.info_of_state gensym_state)
            (typeof_exn gensym_state expr context TVSet.empty) ) )
  with
  | UndefinedSymbolInTypeInferrer (_, e)
  | TypeError e ->
    print_endline e


let typeof gensym_state context expr =
  try Ok (typeof_exn gensym_state expr context TVSet.empty) with
  | UndefinedSymbolInTypeInferrer (pos, e) ->
    Error (UndefinedSymbolInTypeInferrer (pos, e))
  | TypeError e -> Error (TypeError e)


let type_infer_tests =
  [ (let actually =
       let gensym_state = Type.new_gensym_state () in
       typeof_exn
         gensym_state
         (Expr.Lam
            ( (-1, -1)
            , [ ( Expr.PSym ((-1, -1), "x")
                , Expr.Lam
                    ( (-1, -1)
                    , [ (Expr.PSym ((-1, -1), "y"), Expr.Sym ((-1, -1), "x")) ]
                    ) )
              ] ) )
         []
         TVSet.empty
     in
     ( Printf.sprintf
         "type of K combinator is (-> a b a), actually: %s"
         (snd (Type.string_of_typ (0, 'a') actually))
     , actually
       = Type.Type.TyOp
           ( negpos
           , "->"
           , [ Type.Type.TyVar
                 ( negpos
                 , { Type.TypeVariable.id = 0; name = ""; instance = None } )
             ; Type.Type.TyOp
                 ( negpos
                 , "->"
                 , [ Type.Type.TyVar
                       ( negpos
                       , { Type.TypeVariable.id = 1
                         ; name = ""
                         ; instance = None
                         } )
                   ; Type.Type.TyVar
                       ( negpos
                       , { Type.TypeVariable.id = 0
                         ; name = ""
                         ; instance = None
                         } )
                   ] )
             ] ) ) )
  ; ( "Tagged Unions"
    , let gensym_state = Type.new_gensym_state () in
      let with_stdlib expr =
        Expr.Let
          ( (-1, -1)
          , "Bool"
          , Enum
              (TyTagUnion
                 (negpos, [ ("True", Type.tUnit); ("False", Type.tUnit) ]) )
          , Expr.Let
              ( negpos
              , "Option"
              , Enum
                  (TyTagUnion
                     (negpos, [ ("Some", Type.tU8); ("None", Type.tUnit) ]) )
              , expr ) )
      in
      let tvar name =
        Type.Type.TyVar
          (negpos, { Type.TypeVariable.id = 0; name; instance = None })
      in
      typeof
        gensym_state
        []
        (with_stdlib
           (TaggedValue
              ( "True"
              , tvar "Bool"
              , Expr.Unit (-1, -1) (* Expr.U8 ((-1, -1), 1) *) ) ) )
      (* => Errors, expected Unit got Int *)
      = Ok (TyTagUnion (negpos, [ ("True", Type.tUnit); ("False", Type.tUnit) ]))
      (* Error (TypeError "expected Unit got U8") *) )
  ; ( "Tagged Unions with success"
    , let gensym_state = Type.new_gensym_state () in
      let with_stdlib expr =
        Expr.Let
          ( negpos
          , "Bool"
          , Enum
              (TyTagUnion
                 (negpos, [ ("True", Type.tUnit); ("False", Type.tUnit) ]) )
          , Expr.Let
              ( negpos
              , "Option"
              , Enum
                  (TyTagUnion
                     (negpos, [ ("Some", Type.tU8); ("None", Type.tUnit) ]) )
              , expr ) )
      in
      let tvar name =
        Type.Type.TyVar
          (negpos, { Type.TypeVariable.id = 0; name; instance = None })
      in
      let expr =
        with_stdlib
          (TaggedValue ("Some", tvar "Option", Expr.U8 ((-1, -1), 137)))
      in
      typeof gensym_state [] expr
      = Ok (TyTagUnion (negpos, [ ("Some", Type.tU8); ("None", Type.tUnit) ]))
    )
  ]

(* let () =
 *   let var1 = Type.Type.TyVar (Type.TypeVariable.create ()) in
 *   let var2 = Type.Type.TyVar (Type.TypeVariable.create ()) in
 *   let pair_type = Type.Type.TyOp ("*", [var1; var2]) in
 *   let var3 = Type.Type.TyVar (Type.TypeVariable.create ()) in
 *   let my_context =
 *     StringMap.empty
 *     |> StringMap.add "pair" (Type.tArrow var1 (Type.tArrow var2 pair_type))
 *     |> StringMap.add "true" my_bool
 *     |> StringMap.add "cond"
 *          (Type.tArrow my_bool
 *             (Type.tArrow var3
 *                (Type.tArrow var3 var3)))
 *     |> StringMap.add "zero" (Type.tArrow my_int my_bool)
 *     |> StringMap.add "pred" (Type.tArrow my_int my_int)
 *     |> StringMap.add "times" (Type.tArrow my_int (Type.tArrow my_int my_int))
 *   in let pair =
 *        (Expr.Apply
 *           ((Expr.Apply
 *               ((Expr.Sym "pair"),
 *                (Expr.Apply
 *                   ((Expr.Sym "f"), (Expr.Sym "4")))),
 *             (Expr.Apply
 *                ((Expr.Sym "f"),
 *                 (Expr.Sym "true"))))))
 *      in let examples =
 *           [
 *             (\* factorial *\)
 *             (Expr.Letrec              (\* letrec factorial = *\)
 *                ("factorial",
 *                 Expr.Lam           (\* fun n -> *\)
 *                   ("n",
 *                    Expr.Apply (
 *                        Expr.Apply (     (\* cond (zero n) 1 *\)
 *                            Expr.Apply     (\* cond (zero n) *\)
 *                              (Expr.Sym "cond",
 *                               Expr.Apply (Expr.Sym "zero", Expr.Sym "n")),
 *                            Expr.Sym "1"),
 *                        Expr.Apply (     (\* times n *\)
 *                            Expr.Apply (Expr.Sym "times", Expr.Sym "n"),
 *                            Expr.Apply (
 *                                Expr.Sym "factorial",
 *                                Expr.Apply (Expr.Sym "pred", Expr.Sym "n")
 *                   )))),          (\* in *\)
 *                 Expr.Apply (Expr.Sym "factorial", Expr.Sym "5")));
 *
 *             (\* Should fail
 *              * fun x -> (pair (x 3) (x true))
 *              *\)
 *             Expr.Lam("x",
 *                         Expr.Apply(
 *                             Expr.Apply(Expr.Sym "pair",
 *                                        Expr.Apply(Expr.Sym "x", Expr.Sym "3")),
 *                             Expr.Apply(Expr.Sym "x", Expr.Sym "true")));
 *
 *             (\* (pair (f 3)) (f true) *\)
 *             Expr.Apply(
 *                 Expr.Apply(Expr.Sym "pair", Expr.Apply(Expr.Sym "f", Expr.Sym "4")),
 *                 Expr.Apply(Expr.Sym "f", Expr.Sym "true"));
 *
 *             (\* let f = (fn x -> x) in ((pair (f 4)) (f true)) *\)
 *             Expr.Let("f", Expr.Lam("x", Expr.Sym "x"), pair);
 *
 *             (\* fun f -> f f *\)
 *             (\* This should fail (recursive type definition) *\)
 *             Expr.Lam("f", Expr.Apply(Expr.Sym "f", Expr.Sym "f"));
 *
 *             (\* let g = fun f -> 5 in g g *\)
 *             Expr.Let("g", Expr.Lam("f", Expr.Sym "5"),
 *                      Expr.Apply(Expr.Sym "g", Expr.Sym "g"));
 *
 *             (\* example that demonstrates generic and non-generic variables *\)
 *             (\* fun g -> let f = fun x -> g in pair (f 3, f true) *\)
 *             Expr.Lam("g",
 *                         Expr.Let("f",
 *                                  Expr.Lam("x", Expr.Sym "g"),
 *                                  Expr.Apply(
 *                                      Expr.Apply(
 *                                          Expr.Sym "pair",
 *                                          Expr.Apply(Expr.Sym "f", Expr.Sym "3")),
 *                                      Expr.Apply(Expr.Sym "f", Expr.Sym "true"))));
 *
 *             (\* function composition *\)
 *             (\* fun f -> fun g -> fun arg -> f g arg *\)
 *             Expr.Lam("f",
 *                         Expr.Lam("g",
 *                                     Expr.Lam("arg",
 *                                                 Expr.Apply(
 *                                                     Expr.Sym "g",
 *                                                     Expr.Apply(
 *                                                         Expr.Sym "f",
 *                                                         Expr.Sym "arg")))))
 *
 *
 *           ]
 *         in
 *         List.iter (fun ex -> try_exp my_context ex) examples *)
