let n = "\n"
let nt = "\n\t"
let t = "\t"

let read_whole_file (filename: string): string =
  let ch = open_in filename in
  let s = really_input_string ch (in_channel_length ch) in
  close_in ch;
  s

let runtime = read_whole_file "runtime.c"

type context =
  { name: string
  ; vars: string list
  ; parent: context option
  } [@@deriving yojson]
let string_of_context ctx =
  Yojson.Safe.to_string (context_to_yojson ctx)
type state =
  { lam_number: int
  ; main_code: string
  ; definitions_code: string list
  ; structs_code: string list
  ; lambdas_code: string list
  ; current_context: context option
  }

let generate_lambda generate lam_arg lam_body state =
  let current_lam_number = !state.lam_number in
  state := { !state with lam_number = !state.lam_number + 1 };
  state := { !state with definitions_code =
                           List.append
                             !state.definitions_code
                             [(Util.str
                                 [ "struct fn_"
                                 ; string_of_int current_lam_number
                                 ;"_context_struct;\n"])]};
  let context = { name = Util.str
                           [ "fn_"
                           ; string_of_int current_lam_number
                           ; "_context_struct" ]
                ; parent = !state.current_context
                ; vars = [lam_arg] } in
  state := { !state with current_context = Some context };
  let final_string = Util.str
                       ["makeLambda("
                       ; nt; "fn_"
                       ; string_of_int current_lam_number
                       ; "_lambda_fn,"
                       ; nt ; t;"makeContext("
                       ; nt ; t;"sizeof("
                       ; nt ; t; t; "struct fn_"
                       ; string_of_int current_lam_number
                       ; "_context_struct"
                       ; nt ;"), "
                       ; nt; "ctx)"
                       ; nt ;")"] in
  (match context.parent with
   | Some parent ->
      state := { !state with
                 structs_code = List.append
                                  !state.structs_code
                                  [Util.str
                                     [ "struct fn_" ; string_of_int current_lam_number ; "_context_struct {"
                                       ; "struct " ; parent.name ; " * parent;"
                                       ; nt; "struct value " ; lam_arg; ";"
                                       ; nt; "};"]] };
      let context_filling_up = Util.str ["ctx->"; lam_arg ; " = "; lam_arg; ";"] in
      let body_generated = generate lam_body state in
      state :=
        { !state
        with lambdas_code =
               (List.append
                  !state.lambdas_code
                  [Util.str
                     [ "struct value fn_"; string_of_int current_lam_number; "_lambda_fn(\n"
                       ; t; "struct fn_"; string_of_int current_lam_number; "_context_struct * ctx,"
                       ; nt; "struct value "; lam_arg
                       ;n ; ") {"
                       ; nt ;"// Add argument to the current context, so that it is accessable here and in children"
                       ; nt
                       ; context_filling_up
                       ; nt ; "return "; body_generated; ";"
                       ; n ;"}"
                       ; n]])};
      state := { !state with current_context = Some parent};
      final_string
   | None -> final_string)

let generate_match generate state x = function
  | (Expr.PSym (pos, sym), expr) :: _rest ->
     let the_app = Expr.App (pos,
                             Expr.Lam (pos,
                                       [Expr.PSym (pos, sym),
                                        expr]),
                             x) in
     generate the_app state
  | (PTag (_pos, _tag, _x), _expr) :: _rest ->
     failwith "TODO Tagged unions codegen not done yet"
  | [] -> failwith "Match with no cases - makes no sense"

exception GenerateError of string

let rec generate (expression: Expr.expr) (state: state ref): string =
  let code = ref "" in
  (match expression with
   | Let (pos, name, definition, body) ->
      generate
        (App (pos
             ,Lam (pos, [PSym (pos, name), body])
             ,definition))
        state
   | Letrec (_, _, _, _) ->
      failwith "TODO generate of letrec not yet done"
   | Lam (_, (PSym (_, lam_arg), lam_body)::_rest) ->
      code := Util.str
                [ !code
                ; generate_lambda generate lam_arg lam_body state];
      !code
   | Lam (_, (PTag (_, _, _), _)::_) ->
      failwith "TODO Can't yet codegen lambdas of tags"
   | Lam (_, []) -> failwith "Error - given lambda without cases"
   | Sym (_pos, sym) ->
      let curr_ctx = ref !state.current_context in
      code := Util.str [!code
                       ;"ctx"];
      let break = ref false in
      while ((not (!state.current_context = None))
             && !break = false) do
        (match !curr_ctx with
         | Some ctx ->
            if List.mem sym ctx.vars
            then (code := Util.str [ !code
                                   ; "->"
                                   ; sym];
                  break := true;)
            else
              (curr_ctx := ctx.parent;
               code := Util.str [ !code
                                ; "->parent"];)
         | None -> break := true;)
      done;
      !code
   | Unit _ ->
      code := !code ^ "makeUnit()";
      !code
   | String (_, string) ->
      code := Util.str [ !code
                       ; "makeString(\""
                       ; string
                       ; "\")"];
      !code
   | U8 (_, i) ->
      code := Util.str [ !code
                       ; "makeU8("
                       ; string_of_int i
                       ; ")"];
      !code
   | App(_, Sym (_, my_symbol), expr_to_convert) when my_symbol = "string" ->
      code := Util.str [ !code
                       ; "toString("
                       ; generate expr_to_convert state
                       ; ")"];
      !code
   | App (_, e0, e1) ->
      code := Util.str [ !code
                       ; "callLambda("
                       ; nt ; generate e0 state
                       ; ".actual_value.lambda,"
                       ; nt ; generate e1 state
                       ; ")"];
      !code
   | Tuple (_, _children) ->
      failwith "Think about this now.

What is a tuple concretely? It is a collection which you can match over.

You get from a tuple by matching `(match <1 2 3> <n0 n1 n2> n2)` => `3`

Until I create match, I don't really have to allocate these
"
   | Vector (_, children) ->
     let rec fill_vector children acc =
       (match children with
        | child :: rest ->
          fill_vector rest (Printf.sprintf
                              "rrb_push(\n%s, \n mallocValue(%s))"
                              acc
                              (generate child state))
        | [] -> acc
       ) in
     code := "makeVector(" ^ (fill_vector children "rrb_create()") ^ ")";
     !code
   | Dict (_, keys_values) ->
     let rec fill_dict keys_values acc =
       (match keys_values with
        | (k, v) :: rest ->
          fill_dict rest
            (Printf.sprintf
               "value_hamt_set(\n\t%s, \n\t%s, \n\t%s)"
               acc
               ("mallocValue(" ^ (generate k state) ^ ")")
               ("mallocValue(" ^ (generate v state) ^ ")"))
        | [] -> acc
       ) in
     code := "makeDict(" ^ (fill_dict keys_values "value_hamt_new()") ^ ")";
     !code
   | Set (_, _) ->
      failwith "TODO codegen of set not yet implemented"
   | Ann (_, _, expression) ->
      generate expression state
   | Match (_, x, cases) ->
      let generate_match = generate_match generate state in
      generate_match x cases
   | TaggedValue (_name, _enum, _value) ->
     failwith "Generate C code for TaggedValue"
   | Enum _t ->
     failwith "Generate C code for Enum")

let generate_program expression =
  let state = ref { lam_number = 0
                  ; main_code = ""
                  ; definitions_code = []
                  ; structs_code = []
                  ; lambdas_code = []
                  ; current_context =
                      Some { name = "global_context"
                           ; vars = []
                           ; parent = None}} in
  let new_main_code = generate expression state in
  state := { !state with main_code = new_main_code };
  Util.str [ runtime
           ; "/* definitions_code */\n"
           ; Util.str !state.definitions_code
           ; "/* structs_code */\n"
           ; Util.str !state.structs_code ; "\n"  ; "\n"
           ; "/* lambdas_code */" ; "\n"
           ; Util.str !state.lambdas_code ; "\n" ; "\n"
           ; "int main() {"
           ; nt; "struct global_context* ctx = (struct global_context*)makeContext("
           ; nt ; t; "sizeof(struct global_context), NULL\n"
           ; t ;");\n"
           ; t ;"/* main_code */\n"
           ; t ; "print(toString("; !state.main_code ; "));\n\n"
           ; nt; "return 0;"
           ; n ; "}"
           ; n]

let ocaml_import_tests = [ ("Importing codegen", true)]
