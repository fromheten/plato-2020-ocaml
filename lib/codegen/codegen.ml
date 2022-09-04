let n = "\n"

let nt = "\n\t"

let t = "\t"

let runtime () = Util.read_whole_file "runtime.c"

type context =
  { name : string
  ; vars : string list
  ; parent : context option
  }
[@@deriving yojson]

let json_of_context = Util.comp Yojson.Safe.to_string context_to_yojson

type state =
  { lam_number : int
  ; main_code : string
  ; definitions_code : string list
  ; structs_code : string list
  ; lambdas_code : string list
  ; current_context : context option
  }

let generate_lambda generate lam_arg lam_body state =
  let current_lam_number = !state.lam_number in
  state := { !state with lam_number = !state.lam_number + 1 };
  state :=
    { !state with
      definitions_code =
        List.append
          !state.definitions_code
          [ Util.str
              [ "struct fn_"
              ; string_of_int current_lam_number
              ; "_context_struct;\n"
              ]
          ]
    };
  let context =
    { name =
        Util.str [ "fn_"; string_of_int current_lam_number; "_context_struct" ]
    ; parent = !state.current_context
    ; vars = [ lam_arg ]
    }
  in
  state := { !state with current_context = Some context };
  let final_string =
    Util.str
      [ "makeLambda("
      ; nt
      ; "fn_"
      ; string_of_int current_lam_number
      ; "_lambda_fn,"
      ; nt
      ; t
      ; "makeContext("
      ; nt
      ; t
      ; "sizeof("
      ; nt
      ; t
      ; t
      ; "struct fn_"
      ; string_of_int current_lam_number
      ; "_context_struct"
      ; nt
      ; "), "
      ; nt
      ; "ctx)"
      ; nt
      ; ")"
      ]
  in
  match context.parent with
  | Some parent ->
    state :=
      { !state with
        structs_code =
          List.append
            !state.structs_code
            [ Util.str
                [ "struct fn_"
                ; string_of_int current_lam_number
                ; "_context_struct {"
                ; "struct "
                ; parent.name
                ; " * parent;"
                ; nt
                ; "struct value "
                ; lam_arg
                ; ";"
                ; nt
                ; "};"
                ]
            ]
      };
    let context_filling_up =
      Util.str [ "ctx->"; lam_arg; " = "; lam_arg; ";" ]
    in
    let body_generated = generate lam_body state in
    state :=
      { !state with
        lambdas_code =
          List.append
            !state.lambdas_code
            [ Util.str
                [ "struct value fn_"
                ; string_of_int current_lam_number
                ; "_lambda_fn(\n"
                ; t
                ; "struct fn_"
                ; string_of_int current_lam_number
                ; "_context_struct * ctx,"
                ; nt
                ; "struct value "
                ; lam_arg
                ; n
                ; ") {"
                ; nt
                ; "// Add argument to the current context, so that it is \
                   accessable here and in children"
                ; nt
                ; context_filling_up
                ; nt
                ; "return "
                ; body_generated
                ; ";"
                ; n
                ; "}"
                ; n
                ]
            ]
      };
    state := { !state with current_context = Some parent };
    final_string
  | None -> final_string


exception GenerateError of string

let rec preprocess bound_vars expr =
  (* Util.debugprint
   *   "Codegen.preprocess"
   *   [ ("bound_vars", String.concat ", " bound_vars)
   *   ; ("expr", Expr.string_of_expr expr)
   *   ]; *)
  match expr with
  | Expr.Lam (_pos, [ (PSym (psym_pos, x), body) ]) ->
    Expr.Lam (_pos, [ (PSym (psym_pos, x), preprocess (x :: bound_vars) body) ])
  | Expr.Lam (_pos, (PSym ((_, _), _), _) :: (_, _) :: _) ->
    failwith "preprocess not done for this lambda"
  | Lam (_, (PTag (_, _, _), _) :: _) ->
    failwith "neither done for ptag lambdas"
  | Lam (_, []) -> failwith "neither done for empty lambdas"
  | App (pos, f, x) ->
    App (pos, preprocess bound_vars f, preprocess bound_vars x)
  | Sym (pos, "=") ->
    let x = "=" in
    if List.mem x bound_vars then Sym (pos, x) else Builtin Equals
  | Sym (_, _) -> expr
  | String (_, _)
  | Unit _
  | Bool (_, _)
  | Builtin _
  | U8 (_, _) ->
    expr
  | Vector (pos, members) ->
    Vector (pos, List.map (preprocess bound_vars) members)
  | Tuple (pos, members) -> Tuple (pos, List.map (preprocess bound_vars) members)
  | Set (pos, members) -> Set (pos, List.map (preprocess bound_vars) members)
  | Dict (pos, keys_and_vals) ->
    Dict
      ( pos
      , List.map2
          (fun k v -> (preprocess bound_vars k, preprocess bound_vars v))
          (List.map fst keys_and_vals)
          (List.map snd keys_and_vals) )
  | Ann (pos, t, e) -> Ann (pos, t, preprocess bound_vars e)
  | Let (pos, k, v, body) ->
    Let (pos, k, preprocess bound_vars v, preprocess (k :: bound_vars) body)
  | IfThenElse (pos, cond_e, then_e, else_e) ->
    IfThenElse
      ( pos
      , preprocess bound_vars cond_e
      , preprocess bound_vars then_e
      , preprocess bound_vars else_e )


let rec generate (expression : Expr.expr) (state : state ref) : string =
  Util.debugprint
    "Codegen.generate"
    [ ("expression", Expr.string_of_expr expression) ];
  let code = ref "" in
  match expression with
  (* Here I'm trying to make tail recursion work *)
  (* | Let (pos, name, definition, body) -> * if Expr.VarSet.exists ((=) name)
     (Expr.free_vars definition) * then (\* Let Recursive *\) * else (\*
     Nonrecursive Let *\) *)
  | Let (pos, name, definition, body) ->
    generate
      (App (pos, Lam (pos, [ (PSym (pos, name), body) ]), definition))
      state
  | Lam (_, (PSym (_, lam_arg), lam_body) :: _rest) ->
    code := Util.str [ !code; generate_lambda generate lam_arg lam_body state ];
    !code
  | Lam (_, (PTag (_, _, _), _) :: _) ->
    failwith "TODO Can't yet codegen lambdas of tags"
  | Lam (_, []) -> failwith "Error - given lambda without cases"
  | Sym (_pos, sym) ->
    let curr_ctx = ref !state.current_context in
    code := Util.str [ !code; "ctx" ];
    let break = ref false in
    while (not (!state.current_context = None)) && !break = false do
      match !curr_ctx with
      | Some ctx ->
        if List.mem sym ctx.vars
        then (
          code := Util.str [ !code; "->"; sym ];
          break := true )
        else (
          curr_ctx := ctx.parent;
          code := Util.str [ !code; "->parent" ] )
      | None -> break := true
    done;
    !code
  | Unit _ ->
    code := !code ^ "makeUnit()";
    !code
  | String (_, string) ->
    code := Util.str [ !code; "makeString(\""; string; "\")" ];
    !code
  | U8 (_, i) ->
    code := Util.str [ !code; "makeU8("; string_of_int i; ")" ];
    !code
  | App (_, Builtin Equals, _e0) -> failwith "yo chikit utt"
  | App (_, App (_, Builtin Equals, e0), e1) ->
    code :=
      Printf.sprintf
        "%sequals(%s, %s)"
        !code
        (generate e0 state)
        (generate e1 state);
    !code
  | App (_, App (_, Builtin GreaterThan, e0), e1) ->
    let s0 = generate e0 state in
    let s1 = generate e1 state in
    code := Printf.sprintf "%sgreater_than(%s %s)" !code s0 s1;
    !code
  | App (_, Sym (_, my_symbol), expr_to_convert) when my_symbol = "string" ->
    code := Util.str [ !code; "toString("; generate expr_to_convert state; ")" ];
    !code
  | App (_pos, App (_, Sym _, Sym (_, tag)), value) when Util.pascal_case tag ->
    Printf.sprintf
      "makeTaggedValue(\"%s\", (struct value*)mallocValue(%s))"
      tag
      (generate value state)
  | App (_, e0, e1) ->
    code :=
      Util.str
        [ !code
        ; "callLambda("
        ; nt
        ; generate e0 state
        ; ".actual_value.lambda,"
        ; nt
        ; generate e1 state
        ; ")"
        ];
    !code
  | Tuple (_, _children) ->
    failwith
      "Think about this now.\n\n\
      \     What is a tuple concretely? It is a collection which you can match \
       over.\n\n\
      \     You get from a tuple by matching `(match <1 2 3> <n0 n1 n2> n2)` \
       => `3`\n\n\
      \     Until I create match, I don't really have to allocate these\n\
      \     "
  | Vector (_, children) ->
    let rec fill_vector children acc =
      match children with
      | child :: rest ->
        fill_vector
          rest
          (Printf.sprintf
             "rrb_push(\n%s, \n mallocValue(%s))"
             acc
             (generate child state) )
      | [] -> acc
    in
    code := "makeVector(" ^ fill_vector (List.rev children) "rrb_create()" ^ ")";
    !code
  | Dict (_, keys_values) ->
    let rec fill_dict keys_values acc =
      match keys_values with
      | (k, v) :: rest ->
        fill_dict
          rest
          (Printf.sprintf
             "value_hamt_set(\n\t%s, \n\t%s, \n\t%s)"
             acc
             ("mallocValue(" ^ generate k state ^ ")")
             ("mallocValue(" ^ generate v state ^ ")") )
      | [] -> acc
    in
    code := "makeDict(" ^ fill_dict keys_values "value_hamt_new()" ^ ")";
    !code
  | Set (_, _) -> failwith "TODO codegen of set not yet implemented"
  | Ann (_, _, expression) -> generate expression state
  | Bool (_pos, b) ->
    code := "makeBool(" ^ string_of_bool b ^ ")";
    !code
  | IfThenElse (_pos, cond_e, then_e, else_e) ->
    let cond_c = generate cond_e state in
    let then_c = generate then_e state in
    let else_c = generate else_e state in
    code := Printf.sprintf "callIf(%s, %s, %s)" cond_c then_c else_c;
    !code
  | Builtin builtin ->
    failwith
      (Printf.sprintf
         "Codegen can't do anything with a builtin outside of an App.\n\
         \         builtin: %s"
         (Expr.show_builtin builtin) )


let generate_program expression =
  let state =
    ref
      { lam_number = 0
      ; main_code = ""
      ; definitions_code = []
      ; structs_code = []
      ; lambdas_code = []
      ; current_context =
          Some { name = "global_context"; vars = []; parent = None }
      }
  in
  let new_main_code = generate expression state in
  state := { !state with main_code = new_main_code };
  Util.str
    [ runtime ()
    ; "/* definitions_code */\n"
    ; Util.str !state.definitions_code
    ; "/* structs_code */\n"
    ; Util.str !state.structs_code
    ; "\n"
    ; "\n"
    ; "/* lambdas_code */"
    ; "\n"
    ; Util.str !state.lambdas_code
    ; "\n"
    ; "\n"
    ; "int main() {"
    ; nt
    ; "struct global_context* ctx = (struct global_context*)makeContext("
    ; nt
    ; t
    ; "sizeof(struct global_context), NULL\n"
    ; t
    ; ");\n"
    ; t
    ; "/* main_code */\n"
    ; t
    ; "print(toString("
    ; !state.main_code
    ; "));\n\n"
    ; nt
    ; "return 0;"
    ; n
    ; "}"
    ; n
    ]


let ocaml_import_tests = [ ("Importing codegen", true) ]
