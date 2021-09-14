(* This is the main entrypoint of the Plato compiler *)

let compile (src: string): (string, string) result =
  let gensym_env = (Type.new_gensym_state ()) in
  match Read.expression
          gensym_env
          (0
          ,(Util.char_list src)) with
  | Ok (_rest, expr) ->
     let new_env () = (Type.new_gensym_state ()) in
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
         | Ok typ -> Printf.printf "\nType: %s\n" (Type.Type.to_string (Type.new_gensym_state ()) typ);
                     Ok (Type.Type.to_string (new_env ()) typ)
         | Error e -> Error e) with
      | Ok _typ -> Ok (Codegen.generate_program expr)
      | Error e -> Error (match e with
                          | Type_infer.ParseError msg  ->
                             "ParseError: " ^  msg
                          | Type_infer.TypeError msg ->
                             "TypeError: " ^  msg
                          | Type_infer.UnificationError msg ->
                             "UnificationError: " ^  msg))
  | Error e ->
     Error (Util.str ["`Platoc.compile` Error: e: "
                     ;e])

let test test_msg_pairs =
  test_msg_pairs
  |> List.map (fun (msg, test) ->
         if test
         then Util.str [(* "OK: "; msg *)]
         else Util.str ["Error: "; msg])
  |> List.filter (fun s -> String.length s > 0)
  |> (fun testcases ->
    testcases
  |> List.cons (Util.str ["Passing tests: "
                         ;string_of_int ((List.length test_msg_pairs) - (List.length testcases))
                         ;". Failing tests: "
                         ;string_of_int (List.length testcases)
                         ]))
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
