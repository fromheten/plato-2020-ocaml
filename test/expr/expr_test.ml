let rec test acc = function
  | (msg, test_result) :: rest ->
    if test_result
    then test (msg :: fst acc, snd acc) rest
    else test (fst acc, msg :: snd acc) rest
  | [] -> (List.rev (fst acc), List.rev (snd acc))


let free_vars_tests =
  [ ( "finds free/possibly recursive variables"
    , Expr.VarSet.equal
        (Expr.VarSet.of_list [ "iterate"; "x" ])
        (Expr.free_vars (Read.parse_dangerously "(iterate x)")) )
  ; ( "free vars in a let"
    , Expr.VarSet.equal
        (Expr.VarSet.of_list [ "n" ])
        (Expr.free_vars (Read.parse_dangerously "(let f (f n)\n (f (u8 2)))"))
    )
  ; ( "Free var in λ"
    , Expr.VarSet.equal
        (Expr.VarSet.of_list [ "y" ])
        (Expr.free_vars (Read.parse_dangerously "(λ x y)")) )
  ; (let result =
       Expr.free_vars
         (Read.parse_dangerously
            "(λ x (λ n (if ((= n) (u8 0)) x ((iterate x) ((- n) (u8 1))))))" )
     in
     let expected = Expr.VarSet.of_list [ "-"; "="; "iterate" ] in
     ( Printf.sprintf
         "Find the nested free_var! Expected: %s Result: %s"
         (Expr.show_varset expected)
         (Expr.show_varset result)
     , Expr.VarSet.equal expected result ) )
  ]


let () =
  let successes, failures =
    test
      ([], [])
      (List.concat
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
         ; free_vars_tests
         ; Cps.cps_tests
           (* ; Type_infer.type_infer_tests
            * ; Type_infer.fresh_tests *)
           (* ; Type.type_tests *)
         ] )
  in
  if List.length failures > 0
  then (
    Printf.eprintf "Test errors:\n%s" (String.concat "\n" failures);
    exit 1 )
  else (
    Printf.eprintf "Test successes:\n%s" (String.concat "\n" successes);
    exit 0 )
