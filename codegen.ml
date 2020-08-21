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
  }

type state =
  { lam_number: int
  ; main_code: string
  ; definitions_code: string list
  ; structs_code: string list
  ; lambdas_code: string list
  ; current_context: context option
  }

type cmd =
  | LogCmd

type expr =
  | App of expr * expr
  | Lam of string * expr
  | Sym of string
  | String of string
  | Integer of int
  | Command of cmd

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

      (* state := { !state with current_context = Some parent}; *)
      final_string
   | None -> final_string)

let rec generate expression state =
  let code = ref "" in
  (match expression with
   | Lam (lam_arg, lam_body) ->
      code := Util.str
                [ !code
                ; generate_lambda generate lam_arg lam_body state];
      !code
   | Sym sym ->
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
   | String string ->
      code := Util.str [ !code
                       ; "makeString(\""
                       ; string
                       ; "\")"];
      !code
   | Integer i ->
      code := Util.str [ !code
                       ; "makeInteger("
                       ; string_of_int i
                       ; ")"];
      !code
   | App (Command LogCmd, expression_to_print) ->
      code := Util.str [ !code
                       ; "print("
                       ; generate expression_to_print state

                       ; ")"];
      !code
   | App (e0, e1) ->
      code := Util.str [ !code
                       ; "callLambda("
                       ; nt ; generate e0 state
                       ; ".actual_value.lambda,"
                       ; nt ; generate e1 state
                       ; ")"];
      !code
   | Command _ -> failwith "A command should be applied")

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
           ; t ; !state.main_code ; ";\n\n"
           ; nt; "return 0;"
           ; n ; "}"
           ; n]

let ocaml_import_tests = [ ("Importing codegen", true)]
