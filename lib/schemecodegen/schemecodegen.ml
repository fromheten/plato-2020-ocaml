let rec generate = function
  | Expr.Lam (_pos, [PSym (_psym_pos, x), body] ) ->
    Printf.sprintf "(lambda (%s) %s)" x (generate body)
  | Expr.Lam (_, _) -> failwith "can't handle this lambda"
  | Expr.App (_, lambda, given_arg) ->
    Printf.sprintf "(%s %s)" (generate lambda) (generate given_arg)
  | Expr.Sym (_, symbol) -> symbol (* Maybe escape here *)
  | Expr.U8 (_, u8)  -> string_of_int u8
  | Expr.String (_, s) -> Printf.sprintf "\"%s\"" s
  | Expr.Tuple (_pos, xs) -> Printf.sprintf "(list %s)" (String.concat " " (List.map generate xs))
  | Expr.Bool (_, true) -> "#t"
  | Expr.Bool (_, false) -> "#f"
  | Expr.Unit (_) -> "ウニット"
  | Expr.Vector (_pos, xs) -> Printf.sprintf "(list %s)" (String.concat " " (List.map generate xs))
  | Expr.Set (_pos, xs) -> Printf.sprintf "(list %s)" (String.concat " " (List.map generate xs))
  | Expr.Dict (_pos, keys_and_vals) ->
    let scheme_list_of_xs xs =
      Printf.sprintf "(list %s)" (String.concat " " (List.map generate xs)) in
    Printf.sprintf "(list %s)" (String.concat "\n\t" (List.map (fun (key, value) -> scheme_list_of_xs [key; value]) keys_and_vals))
  | Expr.Ann (_pos, _t, e) -> generate e
  | Expr.Let (_, x, given_value, body) ->
    Printf.sprintf "(let ((%s %s)) %s)" x (generate given_value) (generate body)
  | Expr.IfThenElse (_pos, cond, then_e, else_e) ->
    Printf.sprintf "(if %s\n\t %s\n\t %s)" (generate cond) (generate then_e) (generate else_e)
  | Expr.Builtin _builtin -> failwith "Can't handle builtint now"
