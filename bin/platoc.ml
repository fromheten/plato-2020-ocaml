(* This is the main entrypoint of the Plato compiler *)

let rec codegen_expr: (Expr.expr -> (Codegen.expr, string) result) = function
  | Expr.Lam (_pos
              ,(PSym (_pos_psym
                     ,arg)
               ,expr)
               :: _rest) ->
     (match codegen_expr expr with
      | Ok body ->
         Ok (Codegen.Lam (arg, body))
      | Error e ->
         Error (Util.str [ "codegen_expr error: "
                         ; e]))
  | Expr.App (_pos_app
              ,e0
             ,e1) ->
     (match (codegen_expr e0, codegen_expr e1) with
      | (Ok e0, Ok e1) ->
         Ok (Codegen.App (e0, e1))
      | (Error error0, Ok _e1) ->
         Error (Util.str ["codegen_expr error0 = ["
                         ;error0
                         ;"]"])
      | (Ok _e0, Error error1) ->
         Error (Util.str ["codegen_expr error1 = <"
                         ;error1
                         ;">"])
      | (Error error0, Error error1) ->
         Error (Util.str ["codegen_expr error0 = ("
                         ;error0
                         ;")error1 = ("
                         ;error1
                         ;")"]))
  | Expr.Sym (_pos, s) ->
     Ok (Codegen.Sym s)
  | Expr.String (_pos, s) ->
     Ok (Codegen.String s)
  | Expr.U8 (_pos, n) ->
     Ok (Codegen.Integer n)
  | Expr.Tuple (_pos, children) ->
     let codegenned_children =
       (Util.list_result_of_result_list
          (List.map codegen_expr children)) in
     (match codegenned_children with
      | Ok children ->
        Ok (Codegen.Tuple children)
     | Error errs -> Error
                       (String.concat ""
                          ("failed to codegen Tuple children"
                           :: errs)))
  | Expr.Match (pos, value, cases) ->
     codegen_expr (Expr.App (pos, Expr.Lam (pos, cases), value))
  | Expr.Let (_pos, name, definition, body) ->
     (match (codegen_expr definition, codegen_expr body) with
      | Ok def, Ok bod ->
         Ok (Codegen.Let (name, def, bod))
      | Error e, _| _, Error e -> Error e)
  | Expr.Ann (_pos, _t, e) -> codegen_expr e
  | Expr.Vector (_pos, xs) ->
    (match (Util.all_oks (List.map codegen_expr xs)) with
     | Ok children ->
       Ok (Codegen.Vector children)
     | Error errs ->
       failwith (String.concat "\n" errs))
  | Expr.Dict (_pos, keys_values) ->
    let keys = List.map fst keys_values in
    let values = List.map snd keys_values in
    (match (Util.all_oks (List.map codegen_expr keys), Util.all_oks (List.map codegen_expr values)) with
     | (Ok keys, Ok values) ->
       Ok (Codegen.Dict (List.combine keys values))
     | _ -> failwith "Can't convert Dict to codegen expression")
  | _ -> failwith "can't convert this to codegen expression"

let cmdise = function
  | Codegen.App ( Codegen.Sym print_sym
                , other_expressions)
       when print_sym = "Log" ->
     Ok (Codegen.App ( Codegen.Command Codegen.LogCmd
                     , other_expressions))
  | _ ->
     failwith "It seems your program returns something other than an effect.
     An effect can only be `Log` currently.
     Make your program start with applying Log.
     Here is an example: `(Log your-program)`.
     cmdise can only handle programs that begin with applying Log"

let compile (src: string): (string, string) result =
  let gensym_env = (Type.new_env ()) in
  match Read.expression
          gensym_env
          (0
          ,(Util.char_list src)) with
  | Ok (_rest, expr) ->
     let new_env () = (Type.new_env ()) in
     let env = (new_env ()) in
     let stdlib =
       [("Bool", Type.Type.TyTagUnion (["True", Type_infer.my_Unit
                                             ;"False", Type_infer.my_Unit]))
       ;("Command", Type.Type.TyTagUnion
                      (["Log", Type.Function.create

                                 Type_infer.my_String
                                 Type_infer.my_Unit]))
       ;("string", Type.Function.create (Type_infer.ty_var env) Type_infer.my_String)
        (* ("Bool", Type_infer.my_Bool) *)] in
     (match
        (match (Type_infer.analyze_result
                  env
                  stdlib
                  expr) with
         | Ok typ -> Printf.printf "\nType: %s\n" (Type.Type.to_string (Type.new_env ()) typ);
                     Ok (Type.Type.to_string (new_env ()) typ)
         | Error e -> Error e) with
      | Ok _typ -> (match codegen_expr expr with
                   | Ok codegen_expr ->
                      (match cmdise codegen_expr with
                       | Ok program ->
                          Ok (Codegen.generate_program program)
                       | Error e -> Error (Util.str [ "cmdise expr error: "
                                                    ; e]))
                   | Error inner_err ->
                      Error (Util.str ["inner fail: "
                                      ;inner_err]))
      | Error e -> Error (match e with
                          | Type_infer.ParseError msg  ->
                             "ParseError: " ^  msg
                          | Type_infer.TypeError msg ->
                             "TypeError: " ^  msg
                          | Type_infer.UnificationError msg ->
                             "UnificationError: " ^  msg)

      (* try raise exn
       * with | Type_infer.ParseError e | Type_infer.TypeError e ->
       *         Error e *))
  (* (Util.do_then
        *  (Util.do_then_error
        *     (Type_infer.analyze_result
        *        env
        *        stdlib
        *        (Type_infer.Expr.from_read_expr expr))
        *     (fun typ ->
        *       Printf.printf "Type: %s\n" (Type.Type.to_string (new_env ()) typ);
        *       Ok (Type.Type.to_string (new_env ()) typ))
        *     (fun error ->
        *       (try raise error
        *        with | Type_infer.ParseError e | Type_infer.TypeError e ->
        *                Error e)))
        *  (fun _typ ->
        *    (match codegen_expr expr with
        *     | Ok codegen_expr ->
        *        (match cmdise codegen_expr with
        *         | Ok program ->
        *            Ok (Codegen.generate_program program)
        *         | Error e -> Error (Util.str [ "cmdise expr error: "
        *                                      ; e]))
        *     | Error inner_err ->
        *        Error (Util.str ["inner fail: "
        *                        ;inner_err])))) *)
  | Error e ->
     Error (Util.str ["`Platoc.compile` Error: e: "
                     ;e])

let compile_tests =
  [((Util.str ["compile"])
   , true)
  ; ( "LogCmd can be done - temp fix until Unions are implemented"
    , cmdise (Codegen.App ( Codegen.Sym "Log"
                          , Codegen.App
                              ( Codegen.App
                                  ( Codegen.Lam
                                      ( "first"
                                      , Codegen.Lam
                                          ( "second"
                                          , Codegen.Sym "first"))
                                  , Codegen.String "Hello first")
                              , Codegen.String "Bye!")))
      = Ok (Codegen.App
              (Codegen.Command Codegen.LogCmd
              ,Codegen.App
                 (Codegen.App
                    ( Codegen.Lam
                        ( "first"
                        , Codegen.Lam
                            ( "second"
                            , Codegen.Sym "first"))
                    , Codegen.String "Hello first")
                 , Codegen.String "Bye!"))))]

let test test_msg_pairs =
  test_msg_pairs
  |> List.map (fun (msg, test) ->
         if test
         then Util.str ["OK: "; msg]
         else Util.str ["Error: "; msg])
  |> List.filter (fun s -> String.length s > 0)
  |> (fun testcases ->
    testcases
  (* |> List.cons (Util.str ["Failing tests: "
     *                        ;string_of_int (List.length testcases)]) *))
  |> String.concat "\n"

let print_tests_results =
  List.concat
    [ Read.literal_tests
    ; Read.quoted_symbol_test
    ; Read.strip_starting_spaces_tests
    ; Read.n_or_more_tests
    ; Read.lambda_tests
    ; Read.symbol_tests
    ; Read.set_tests
    ; Read.vector_tests
    ; Read.expression_tests
    ; Read.tunit_tests
    ; Read.typ_tests
    ; Read.string_tests
    ; Codegen.ocaml_import_tests
    ; compile_tests
    ; Read.string_of_expr_tests
    ; Type_infer.type_infer_tests]
  |> test

let version = "0.0.0.0.0.1"

let help_string = "Syntax: $ platoc <options> <input-files.plato>

                   Options:
                   * `-o` or `--output`: output a machine runnable program, e.g. `platoc -o /path/to/executeable myprogram.plato`
                   * `-oc` or `--output-c`: Generate C code from your Plato program into a file, e.g. `platoc -oc /path/to/c_source.c myprogram.plato`
                   * `--run <source file>`: Compile a file containing plato source code and run the resulting program
                   * `--publish` publishes from stdin and prints the hash ID to stdout
                   * `--tests` to show test results
                   "

let welcome_text =
  String.concat "\n" ["# Welcome to the Plato platform."
                     ;"I hope you enjoy it!\n"
                     ;help_string]

let () =
  print_string (Util.str ["platoc version: "
                         ;version]);
  print_newline ();
  match Read.parse_args (0
                         ,(Util.char_list
                             (String.concat
                                " "
                                (Array.to_list
                                   Sys.argv)))) with
  | Ok (_rest, Read.PrintHelp _) ->
     print_string help_string
  | Ok (_rest, Read.ShowPrintTests _) ->
     print_tests_results
     |> print_string
     |> print_newline
     |> print_newline
  | Ok (_rest, Read.OutputExeToPath (_pos, _io_paths)) ->
     failwith "can't do this anymore"
  | Ok (_rest, Read.OutputCToPath (_pos, io_paths)) ->
     let src = Util.str (List.map
                           Codegen.read_whole_file
                           io_paths.input_files) in
     (match compile src with
      | Ok c_source ->
     (* Write message to file *)
         let oc = open_out io_paths.output_file in    (* create or truncate file, return channel *)
         Printf.fprintf oc "%s\n" c_source;           (* write something *)
         close_out oc;                                (* flush and close the channel *)
      | Error e ->
         print_string (Util.str [ "Compilation Error: "
                                ; e]))
  | Ok(_, Run (_pos, src_path)) ->
     let src = (Codegen.read_whole_file src_path) in
     let out_path = "/tmp/plato_run_temp" in
     let c_out_path = String.concat "" [out_path; ".c"] in
     (match compile src with
      | Ok c_source ->
         (* Write message to file *)
         let oc = open_out c_out_path in
         Printf.fprintf oc "%s\n" c_source;
         close_out oc;
      | Error e ->
        print_string (Util.str [ "Compilation Error: "
                                ; e]));
     let prefix = "/Users/martin/code/plato-2020-ocaml/thirdparty/target" in
     let compile_command = (String.concat
                              ""
                              [ Printf.sprintf "LDFLAGS='-L%s/lib' CFLAGS='-I%s/include' " prefix prefix
                              ; "cc -o "
                              ; out_path
                              (* ; " -v " *)
                              ; " -I" ^ prefix ^ "/include "
                              ; " -L" ^ prefix ^ "/lib "
                              ; " -lgc -lrrb -lsds "
                              ; c_out_path
                              (* ; " && rm " ;c_out_path *)
                              ; " && /tmp/plato_run_temp"]) in
     let status_code = Sys.command compile_command in
     exit status_code;
  | Ok (_, PublishAndPrintIDFromSTDIN (_pos)) ->
    (* print_string (Cryptokit.hash_channel (Cryptokit.Hash.sha3 512) Stdlib.stdin); *)
     let binary_hash = (Cryptokit.hash_string (Cryptokit.Hash.sha3 512) "Hello") in
     failwith binary_hash
  (* let hash_id = Platoid.base64_encode (Util.char_list binary_hash) in
      * print_string hash_id;
      * print_newline (); *)
  | Ok (_, Read.NoCommandArguments (_pos)) ->
     print_string welcome_text
  | Error e ->
     Printf.fprintf stderr "%s\n" ( Util.str [ "Argument parsing error: given argument is: "
                                             ; String.concat " " (Array.to_list Sys.argv)]);
     Printf.fprintf stderr "%s\n" e
