(* This is the main entrypoint of the Plato compiler *)

let rec codegen_expr: (Read.expr -> (Codegen.expr, string) result) = function
  | Read.Lam (_pos
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
  | Read.App (_pos_app
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
                         ;")"
     ]))
  | Read.Sym (_pos, s) ->
     Ok (Codegen.Sym s)
  | Read.String (_pos, s) ->
     Ok (Codegen.String s)
  | Read.U8 (_pos, n) ->
     Ok (Codegen.Integer n)
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

let compile (src: string) =
  match Read.expression (0
                         ,(Read.char_list src)) with
  | Ok (_rest, expr) ->
     (match Unify.infer_and_unify expr with
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
      | Error e -> failwith e)
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
         then Util.str [(* "OK: "; msg *)]
         else Util.str ["Error: "; msg])
  |> List.filter (fun s -> String.length s > 0)
  |> (fun testcases ->
    testcases
    |> List.cons (Util.str ["Failing tests: "
                           ;string_of_int (List.length testcases)]))
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
    ; Unify.unify_tests
    ; Read.string_of_expr_tests
    ; Unify.infer_tests]
  |> test

let version = "0.0.0.0.0.1"

let () =
  print_string (Util.str ["platoc version: "
                         ;version]);
  print_newline ();
  match Read.parse_args (0
                         ,(Read.char_list
                             (String.concat
                                " "
                                (Array.to_list
                                   Sys.argv)))) with
  | Ok (_rest, Read.PrintHelp _) ->
     print_string "Thanks for trying Plato!

                   Syntax: $ platoc <options> <input-files.plato>

                   Options:
                   * `-o` or `--output`: output a machine runnable program, e.g. `platoc -o /path/to/executeable myprogram.plato`
                   * `-oc` or `--output-c`: Generate C code from your Plato program into a file, e.g. `platoc -oc /path/to/c_source.c myprogram.plato`
                   * `--publish` publishes from stdin and prints the hash ID to stdout
                   "
  | Ok (_rest, Read.ShowPrintTests _) ->
     print_tests_results
     |> print_string
     |> print_newline
     |> print_newline
  | Ok (_rest, Read.OutputExeToPath (_pos, io_paths)) ->
     print_string "Compiling Plato to C...";
     let src = Util.str (List.map
                           Codegen.read_whole_file
                           io_paths.input_files) in
     print_string "DONE"; print_newline ();
     (match compile src with
      | Ok c_source ->
         (let c_file = Util.str [io_paths.output_file
                                ;".c"] in
          (* Write C source to intermediate file *)
          print_string (Util.str ["Writing C source to intermediate file ("
                                 ;c_file
                                 ;")..."]);
          let out_channel = open_out c_file in        (* create or truncate file, return channel *)
          Printf.fprintf out_channel "%s\n" c_source; (* write something *)
          close_out out_channel;                      (* flush and close the channel *)
          print_string "DONE"; print_newline ();
          print_string "Compiling from C to binary...";
          if (Sys.command (Util.str [ "cc "
                                    ; c_file
                                    ; " -o "
                                    ; io_paths.output_file])) = 0
          then (print_string "DONE"; print_newline ();)
          else failwith "Failed compiling the output to native code executeable";
         )
      | Error e ->
         print_string (Util.str [ "Compilation Error: "
                                ; e]);
         print_newline ())
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
  | Ok (_, PublishAndPrintIDFromSTDIN (_pos)) ->
     (* print_string (Cryptokit.hash_channel (Cryptokit.Hash.sha3 512) Stdlib.stdin); *)
     let binary_hash = (Cryptokit.hash_string (Cryptokit.Hash.sha3 512) "Hello") in
     failwith binary_hash
     (* let hash_id = Platoid.base64_encode (Read.char_list binary_hash) in
      * print_string hash_id;
      * print_newline (); *)
  | Error e ->
     Printf.fprintf stderr "%s\n" ( Util.str [ "Argument parsing error: given argument is: "
                                             ; String.concat " " (Array.to_list Sys.argv)]);
     Printf.fprintf stderr "%s\n" e
