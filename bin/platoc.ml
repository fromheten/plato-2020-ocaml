(* This is the main entrypoint of the Plato compiler *)
let negpos = (-1, -1)

let stdlib_types =
  [ ( "="
    , Hmtype.TypeScheme
        ( [ "left__2"; "right__3" ]
        , [ Hmtype.TypeConstant Hmtype.Arrow
          ; Hmtype.TypeVariable "left__2"
          ; Hmtype.TypeApp
              [ Hmtype.TypeConstant Hmtype.Arrow
              ; Hmtype.TypeVariable "right__3"
              ; Hmtype.TypeConstant Hmtype.Boolean
              ]
          ] ) )
  ]


let stdlib = [ (Expr.PSym (negpos, "="), Expr.Builtin Equals) ]

let rec add_stdlib stdlib expr =
  match stdlib with
  | (k, v) :: rest_of_stdlib ->
    Expr.App
      (negpos, Expr.Lam (negpos, [ (k, add_stdlib rest_of_stdlib expr) ]), v)
  | [] -> expr


let compile (src : string) : (string, string) result =
  match Read.expression (0, Util.char_list src) with
  | Ok (_rest, expr) ->
    Printf.printf "\nExpr: %s\n" (Expr.string_of_expr expr);
    let type_result = Ok (Expr.infer stdlib_types expr) in
    ( match type_result with
    | Ok typ ->
      Printf.printf "Type: %s" (Hmtype.string_of_typ typ);
      let expr_preprocessed = Codegen.preprocess [] expr in
      (* Util.debugprint
       *   "Platoc Compile"
       *   [ ("src", src)
       *   ; ("expr_preprocessed", Expr.show_expr expr_preprocessed)
       *   ]; *)
      Ok (Codegen.generate_program expr_preprocessed)
    | Error e -> failwith (Printf.sprintf "Compilation error: %s" e) )
  | Error e -> Error (Util.str [ "`Platoc.compile` Error: e: "; e ])


let version = "0.0.0.0.0.1"

let help_string =
  "Syntax: $ platoc <options> <input-files.plato>\n\n\
  \                   Options:\n\
  \                   * `-o` or `--output`: output a machine runnable program, \
   e.g. `platoc -o /path/to/executeable myprogram.plato`\n\
  \                   * `-oc` or `--output-c`: Generate C code from your Plato \
   program into a file, e.g. `platoc -oc /path/to/c_source.c myprogram.plato`\n\
  \                   * `--run <source file>`: Compile a file containing plato \
   source code and run the resulting program\n\
  \                   * `--publish` publishes from stdin and prints the hash \
   ID to stdout\n\
  \                   "


let welcome_text =
  String.concat
    "\n"
    [ "# Welcome to the Plato platform."
    ; "I hope you enjoy it!\n"
    ; help_string
    ]


let () =
  print_string (Util.str [ "platoc version: "; version ]);
  print_newline ();
  match
    Read.parse_args
      (0, Util.char_list (String.concat " " (Array.to_list Sys.argv)))
  with
  | Ok (_rest, Read.PrintHelp _) -> print_string help_string
  | Ok (_rest, Read.OutputExeToPath (_pos, _io_paths)) ->
    failwith "can't do this anymore"
  | Ok (_rest, Read.OutputCToPath (_pos, io_paths)) ->
    let src =
      Util.str (List.map Codegen.read_whole_file io_paths.input_files)
    in
    ( match compile src with
    | Ok c_source ->
      (* Write message to file *)
      let oc = open_out io_paths.output_file in
      (* create or truncate file, return channel *)
      Printf.fprintf oc "%s\n" c_source;
      (* write something *)
      close_out oc
      (* flush and close the channel *)
    | Error e -> print_string (Util.str [ "Compilation Error: "; e ]) )
  | Ok (_, Run (_pos, src_path)) ->
    let src = Codegen.read_whole_file src_path in
    let out_path = "/tmp/plato_run_temp" in
    let c_out_path = String.concat "" [ out_path; ".c" ] in
    ( match compile src with
    | Ok c_source ->
      (* Write message to file *)
      let output_file_channel = open_out c_out_path in
      Printf.fprintf output_file_channel "%s\n" c_source;
      close_out output_file_channel
    | Error e -> print_string (Util.str [ "Compilation Error: "; e ]) );
    let prefix = "/Users/martin/code/plato-2020-ocaml/thirdparty/target" in
    let compile_command =
      String.concat
        ""
        [ Printf.sprintf
            "LDFLAGS='-L%s/lib' CFLAGS='-I%s/include' "
            prefix
            prefix
        ; "cc -o "
        ; out_path (* ; " -v " *)
        ; " -I" ^ prefix ^ "/include "
        ; " -L" ^ prefix ^ "/lib "
        ; " -lgc -lrrb -lsds "
        ; c_out_path (* ; " && rm " ;c_out_path *)
        ; " && /tmp/plato_run_temp"
        ]
    in
    let status_code = Sys.command compile_command in
    exit status_code
  | Ok (_, PublishAndPrintIDFromSTDIN _pos) ->
    (* print_string (Cryptokit.hash_channel (Cryptokit.Hash.sha3 512)
       Stdlib.stdin); *)
    let binary_hash = Cryptokit.hash_string (Cryptokit.Hash.sha3 512) "Hello" in
    failwith binary_hash
  (* let hash_id = Platoid.base64_encode (Util.char_list binary_hash) in *
     print_string hash_id; * print_newline (); *)
  | Ok (_, Read.NoCommandArguments _pos) -> print_string welcome_text
  | Error e ->
    Printf.fprintf
      stderr
      "%s\n"
      (Util.str
         [ "Argument parsing error: given argument is: "
         ; String.concat " " (Array.to_list Sys.argv)
         ] );
    Printf.fprintf stderr "%s\n" e
