type source =
  int * char list               (* index * rest *)

type 'a parseresult =
  (source * 'a, string) result

let is_spacing c =
  (List.exists (fun x -> x = c)
     [ ' '
     ; '\t'
     ; '\n' ])

let incend position = (fst position, (snd position + 1))

let rec strip_starting_spaces (source: source): source =
  match source with
  | (pos, x :: rest) when is_spacing x ->
     strip_starting_spaces (pos + 1, rest)
  | (_pos, x :: _rest) when not (is_spacing x) ->
     source
  | (pos, []) -> (pos, [])
  | (_pos, _x :: _rest) -> failwith "strip_starting_spaces: will never happen"

let strip_starting_spaces_tests =
  [("strip this should work"
   ,strip_starting_spaces (0, (Util.char_list " hello\'  ' "))
    = (1, (Util.char_list "hello\'  ' ")))
  ;("strip starting spaces"
   ,strip_starting_spaces (0, Util.char_list "     hello there")
    = (5, ['h'; 'e'; 'l'; 'l'; 'o'; ' '; 't'; 'h'; 'e'; 'r'; 'e']))]

let string_of_position position =
  Util.str ["position start: "
           ;string_of_int (fst position)
           ;", end: "
           ;string_of_int (snd position)]

let symbol (source: source): Expr.expr parseresult =
  let source = (strip_starting_spaces source) in
  let start_pos: int = (fst source) in
  let rec inner (s: source) (is_escaping: bool) (acc: char list) =
    match (is_escaping, s) with
    (* Skip whitespaces in the beginning *)
    | (false, (_pos, first :: _rest)) when
           List.length acc = 0 && is_spacing first ->
       failwith "should never happen "
    | (false, (pos, first :: rest)) when first = '\\' ->
       inner (pos + 1, rest) true acc
    | (false, (pos, first :: rest)) when Expr.is_symbol_char first ->
       inner (pos + 1, rest) false (first :: acc)
    | (false, (pos, first :: _rest))
         when not (Expr.is_symbol_char first) && List.length acc > 0 ->
       Ok (s
          ,Expr.Sym ((start_pos, pos), Util.string_of_char_list (List.rev acc)))
    | (false, (_pos, first :: rest))
         when not (Expr.is_symbol_char first)
              && List.length acc = 0 ->
       Error (Util.str ["Invalid symbol '"
                       ;Util.string_of_char_list (first :: rest)
                       ;"' from src '"
                       ;Util.string_of_char_list (snd source)
                       ;"'"])
    | (true, (pos, first :: rest)) when not (Expr.is_symbol_char first) ->
       inner (pos + 1, rest) false (first :: acc)
    | (true, (pos, [])) ->
       Error (Util.str ["escaping EOF. "
                       ;string_of_int pos])
    | (false, (pos, [])) when List.length acc > 0 ->
       Ok ((pos, [])
          ,Sym ((start_pos, pos), Util.string_of_char_list (List.rev acc)))
    | ((true, (_, _::_))) -> Error "Should never happen"
    | (false, (_pos, [])) -> Error "`symbol` got an empty string - can't parse that into a Sym"
    | (false, (_pos, _x :: _rest)) -> Error "Lastests option"
  in inner
       source
       false
       []

let map
      (p: source -> 'a parseresult)
      (callback: ((source * 'a), 'err) result -> 'b parseresult)
      (src: source): 'b parseresult =
  callback (p src)

let symbol_native_string =
  map
    symbol
    (function
     | Ok (state, Sym (_sym_pos, result)) ->
        Ok (state, result)
     | Ok ((index, _rest), _) ->
        Error (Util.str ["Result of symbol_native_string not a Symbol - at position "
                        ;string_of_int index])
     | Error e -> Error e)

let symbol_tests =
  [( "Vectors are not symbols"
   , symbol (0
            ,(Util.char_list "[ a b c]"))
     = Error "Invalid symbol '[ a b c]' from src '[ a b c]'")
  ; ("little symbol"
    , symbol (0, (Util.char_list "xyx"))
      = Ok ((3, []), Sym ((0, 3), "xyx")))
  ;("long symbol"
   , symbol (0, (Util.char_list " im-a-symbol the rest of the source string"))
     = Ok ((12, [' '; 't'; 'h'; 'e'; ' '; 'r'; 'e'; 's'; 't'; ' '; 'o'; 'f'; ' '; 't'; 'h';
                 'e'; ' '; 's'; 'o'; 'u'; 'r'; 'c'; 'e'; ' '; 's'; 't'; 'r'; 'i'; 'n'; 'g'])
          ,Sym ((1, 12)
               ,"im-a-symbol")))]

let quoted_symbol (source: source) =
  let src_without_preceding_spacings: source = strip_starting_spaces source in
  match src_without_preceding_spacings with
  | (start_pos, first :: _rest) when first = '\'' ->
     let rec inner (s: source) (is_escaping: bool) acc =
       (match (is_escaping, s) with
        | (false, (pos, first :: rest))
             when List.length acc = 0 && first = '\'' ->
           inner (pos + 1, rest) false acc
        | (false, (pos, first :: rest))
             when first = '\'' ->
           Ok ((pos, rest)
              ,Expr.Sym ((start_pos, pos)
                   ,Util.string_of_char_list (List.rev acc)))
        | (true, (pos, first :: rest))
             when first = '\'' ->
           inner (pos + 1, rest) false (first :: acc)
        | (true, (pos, first :: rest))
             when first = '\\' ->
           inner (pos + 1, rest) false (first :: acc)
        | (false, (pos, first :: rest))
             when first = '\\' ->
           inner (pos + 1, rest) true acc
        | (false, (pos, first :: rest)) ->
           inner (pos + 1, rest) false (first :: acc)
        | (true, (_pos, [])) -> Error "escaping EOF?"
        | _ -> failwith (Util.str [ "is_escaping: "
                                  ; "\""
                                  ; string_of_bool is_escaping
                                  ; "\""
                                  ; "s: \""
                                  ; (Util.string_of_char_list (snd s))
                                  ; "\""]))
     in inner
          src_without_preceding_spacings
          false
          []
  | (pos, []) -> Error (Util.str ["Can't parse empty symbol. Somewhere around position: "
                                 ;string_of_int pos])
  | _ -> Error "Quoted symbols must begin with a single-quote \"'\""

let string (source: source): Expr.expr parseresult =
  let src_without_preceding_spacings = (strip_starting_spaces source) in
  match src_without_preceding_spacings with
  | (start_pos, first :: _rest) when first = '"' ->
     let rec inner
               (s: source)
               (is_escaping: bool)
               (acc: char list): Expr.expr parseresult =
       (match (is_escaping, s) with
        | (false, (pos
                  ,first :: rest))
             when List.length acc = 0 && first = '"' ->
           inner (pos, rest) false acc
        | (false, (pos, first :: rest))
             when first = '"' ->
           Ok ((pos
               ,rest)
              ,String ((start_pos
                       ,pos)
                      ,Util.string_of_char_list (List.rev acc)))
        | (true, (pos
                 ,first :: rest))
             when first = '"' ->
           inner (pos, rest) false (first :: acc)
        | (true, (pos
                 ,first :: rest))
             when first = '\\' ->
           inner (pos + 1, rest) false (first :: acc)
        | (false, (pos, first :: rest)) when first = '\\' ->
           inner (pos + 1, rest) true acc
        | (false, (pos, first :: rest)) ->
           inner (pos + 1
                 ,rest) false (first :: acc)
        | (true, (pos, [])) -> Error (Util.str ["escaping EOF?"
                                               ;string_of_position (start_pos, pos)])
        | _ -> failwith (Util.str [ "is_escaping: "
                                  ; "\""
                                  ; string_of_bool is_escaping
                                  ; "\""
                                  ; "s: \""
                                  ; Util.string_of_char_list (snd s)
                                  ; " after position: "
                                  ; string_of_int (start_pos)
                                  ; "\""]))
     in inner
          src_without_preceding_spacings
          false
          []
  | (start_position, []) -> Error (Util.str ["Can't parse empty String"
                                            ;string_of_int start_position])
  | _ -> Error "Strings must begin with a double-quote \"\"\""

let string_tests =
  [("Strings are parsed"
   , string (0
            ,Util.char_list "  \"Hello\"  ")
     = Ok ((7
           ,[' '; ' '])
          ,String ((2, 7)
                  ,"Hello")))]

let quoted_symbol_test =
  [("Simple quoted symbol with escaped single quote"
   ,quoted_symbol (0
                  ,Util.char_list "   ' hello\\'  ' ")
    = Ok ((14 ,[' '])
         ,Sym ((3, 14)
              ," hello'  ")))
  ;("Quoted symbol without src = single quote should fail"
   ,quoted_symbol (0
                  ,(Util.char_list "a b c"))
    = Error "Quoted symbols must begin with a single-quote \"'\"")
  ;("Empty quoted symbols makes no sense"
   ,quoted_symbol
      (0
      ,(Util.char_list ""))
    = Error "Can't parse empty symbol. Somewhere around position: 0")
  ;("Quoted symbols should src = not parse unless beginning in \"'\""
   ,quoted_symbol (0
                  ,(Util.char_list "#{ 'sym' }# "))
    = Error "Quoted symbols must begin with a single-quote \"'\"")]

let literal (lit: string) (source: source): unit parseresult =
  let lit_list: char list =
    snd (strip_starting_spaces (-1
                               ,(Util.char_list lit))) in
  let rec inner
            (rest_of_lit: char list)
            (curr_source: source)
            (acc: char list) =
    match (rest_of_lit, curr_source) with
    | (lit_first :: lit_rest
      ,(position, src_first :: src_rest))
         when lit_first = src_first ->
       inner lit_rest (position, src_rest) (src_first :: acc)
    | (_lit_first :: _lit_rest
      ,(_position, _src_first :: _src_rest)) ->
       Error
         (Util.str
            ["Source '"
            ;Util.string_of_char_list (snd source)
            ;"' not matching literal '"
            ;lit
            ;"'"])
    | ([], _) ->
       if List.rev acc = lit_list
       then Ok (((fst curr_source) + List.length acc
                ,snd curr_source)
               ,())
       else failwith "Bug in literal"
    | (_lit_first :: _lit_rest, (_position, [])) ->
       Error "Source too short"
  in inner
       lit_list
       (strip_starting_spaces source)
       []

let literal_tests =
  [("literally skip spacesrc = s",
    (literal
       "a"
       (0
       ,(Util.char_list "    aaa")))
    = Ok ((5
          ,['a'; 'a'])
         ,()))
  ;("literally fail with honesty",
    (literal
       "["
       (0
       ,(Util.char_list "#{")))
    = Error "Source '#{' not matching literal '['")]

let andThen p0 p1 (source: source) =
  match p0 source with
  | Ok ((rest_pos, rest), r0) ->
     (match p1 (rest_pos, rest) with
      | Ok ((end_pos, rest), r1) ->
         Ok ((end_pos
             ,rest)
           , (r0, r1))
      | Error e -> Error e)
  | Error e -> Error e

let left p = map p (function | Ok (source, (left, _right))
                               -> Ok (source, left)
                             | Error e -> Error e)
let right p = map p (function | Ok (source, (_left, right))
                                -> Ok (source, right)
                              | Error e ->
                                 Error e)

let n_or_more
      (total_n: int)
      (parse: 'source_code -> 'a parseresult)
    : 'source_code -> ('a list) parseresult =
  let rec inner n acc source =
    match parse source with
    | Ok (src_rest, res) ->
       inner (n + 1) (res :: acc) src_rest
    | Error e ->
       if n >= total_n
       then Ok (source, List.rev acc)
       else Error e
  in inner 0 []

let n_or_more_tests =
  [( "take 4 a"
   , n_or_more
       4
       (literal "a")
       (0 ,(Util.char_list "   aaaaaa "))
     = Ok ((9, [' '])
	  ,[(); (); (); (); (); ()]))]

let orElse p0 p1 (source: source) =
  match p0 source with
  | Ok (rest, r0) -> Ok (rest, r0)
  | Error e0 -> (match p1 source with
                 | Ok (rest, r1) ->
                    Ok (rest, r1)
                 | Error e1 ->
                    Error (Util.str
                             [ "orElse Error src: '"
                             ; Util.string_of_char_list (snd source)
                             ; "'. position: "
                             ; string_of_int (fst source)
                             ; "\ne0:'"
                             ; e0
                             ; "'\ne1:"
                             ; e1]))

let rec orElse_list ps src =
  match ps with
  | p :: [] -> p src
  | p :: ps -> (orElse p (orElse_list ps)) src
  | [] -> Error "orElse_list given no ps"

let vector
      (expression: source -> Expr.expr parseresult)
      (source: source)
    : Expr.expr parseresult =
  (map
     (right (left (andThen
                     (andThen
                        (literal "[")
                        (n_or_more 0 expression))
                     (literal "]"))))
     (function
      | Ok ((pos, src), list) ->
         Ok ((pos, src)
            ,Expr.Vector ((fst source, pos), list))
      | Error e ->
         Error e))
    source

let vector_tests =
  [("this is not a vector",
    vector symbol (0
                  ,(Util.char_list "#{ []}#"))
    = Error "Source '#{ []}#' not matching literal '['")]

let set
      (expr: source -> Expr.expr parseresult)
      (source: source)
    : Expr.expr parseresult =
  (map
     (right (left (andThen
                     (andThen
                        (literal "#{")
                        (n_or_more 0 expr))
                     (literal "}#"))))
     (Util.take_ok (fun ((end_pos, src), list) ->
          let pos: int = end_pos in
          ((pos, src)
          ,Expr.Set ((fst source, pos), list)))))
    source

let set_tests =
  [("empty set"
   ,set symbol (0, (Util.char_list "#{}# ok"))
    = Ok ((4
          ,[' '; 'o'; 'k'])
         ,Set ((0,4)
              ,[])))
  ;("set of sets"
   ,set (set symbol) (0
                     ,(Util.char_list "#{#{}# #{}#}#"))
    = Ok ((13, [])
        , Set ((0, 13)
             , [Set ((2, 6), [])
               ;Set ((6, 11), [])])))
  ;("set of symbol"
   ,set symbol (0, (Util.char_list "#{hello}#"))
    = Ok ((9
          ,[])
        , Set ((0, 9), [Sym ((2, 7), "hello")])))
  ;("set of symbol or quoted_symbol"
   ,set
      (orElse symbol quoted_symbol)
      (0
      ,(Util.char_list "#{'quoted sym' unquoted}# rest of src"))
    = Ok
        ((24
         ,[' '; 'r'; 'e'; 's'; 't'; ' '; 'o'; 'f'; ' '; 's'; 'r'; 'c']),
         Set ((0, 24)
             ,[Sym ((2, 13), "quoted sym")
              ;Sym ((14, 22), "unquoted")])))
  ;("set of a quoted sym"
   ,set quoted_symbol (0, (Util.char_list "#{ 'sym' }# "))
    = Ok ((10, [' '])
         ,Set ((0, 10)
              ,[Sym ((3, 7)
                    ,"sym")])))]

let pattern expression: source -> ('a Expr.pattern) parseresult =
  let symbol_pattern = (map (orElse
                               symbol
                               quoted_symbol)
     (function
      | Ok ((end_pos, rest), Sym (pos, s)) ->
         Ok ((end_pos, rest), Expr.PSym (pos, s))
      | Error e -> Error e
      | _ -> failwith "you made it a result ;-)")) in
  let tag_pattern = (map (andThen (andThen (andThen
																						                        (literal "(")
																						                        (orElse symbol quoted_symbol))
													                        expression)
				                        (literal ")"))
                       (Util.take_ok
                          (function
                           | (source, ((((), Expr.Sym (name_pos, name)), child), ())) ->
                              (source
                              ,Expr.PTag (name_pos, name, child))
                           | _ -> failwith "don't know hwo to handle this"
                    ))) in
  (orElse symbol_pattern tag_pattern)

let lambda (expression: source -> Expr.expr parseresult) (source: source): Expr.expr parseresult =
  let pattern = pattern expression in
  (map (andThen (andThen
                   (andThen
                      (literal "(")
                      (literal "λ"))
                   (n_or_more 1 (andThen
                                   pattern
                                   expression)))
          (literal ")"))
     (function
      | Ok ((new_pos, rest),
            ((((), ())
             , (PSym (psym_pos, x)
               ,body0)
               :: arg_bodies_list)
            , ())) ->
         Ok ((new_pos, rest)
            ,Expr.Lam ((fst source, new_pos) (* TODO make this use the skipped spaces version  *)
                 ,((PSym (psym_pos, x)
                   ,body0) :: arg_bodies_list)))
      | _ -> Error "lambda must contain parameter and body expression"))
    source

let rec undeepen (source: source) (patterns_exps: (Expr.expr list * Expr.expr) list) =
  (* BUG *)
  let inner: (Expr.expr list * Expr.expr) -> (Expr.expr Expr.pattern * Expr.expr) = function
    | ((Sym (psym_pos, first)) :: [], e) ->
       (PSym (psym_pos, first), e)
    | (Sym (psym_pos, first) :: rest, e) ->
       (PSym (psym_pos, first),
        (match undeepen
                 source
                 [(rest, e)] with
         | (_new_source_code, x) -> x))
    | _ -> failwith "undeepen yourself brah"
  in
  (source
  , Lam (((fst source), (fst source) + 1), List.map inner patterns_exps))

let deep_lambda (expr: source -> Expr.expr parseresult) (source: source) =
  (map (andThen
          (andThen
             (andThen
                (literal "(")
                (literal "λ"))
             (n_or_more 1 (andThen (vector expr) expr)))
          (literal ")"))
     (Util.take_ok
        (function | (new_source_code
                    , ((((), ()),
                        patterns_exprs),
                       ())) -> undeepen new_source_code
                                 (List.map
                                    (function
                                     | (Expr.Vector (_vec_pos, v), e) -> (v, e)
                                     | _ -> failwith "Give me vector or give me death")
                                    patterns_exprs))))
    source

let lambda_tests =
  [("λ parse identity"
   ,lambda symbol (0, (Util.char_list "  (λ x x)"))
    (* The indexes are a bit off but whatever *)
    = Ok ((10, []), Lam ((0, 10), [(PSym ((6, 7), "x"), Sym ((8, 9), "x"))])))
  ;("λ multiple patterns"
   ,lambda symbol (0, (Util.char_list "(λ
                                  x x
                                  y y)"))
    = Ok ((80, []),
          Lam ((0, 80),
               [(PSym ((38, 39), "x"), Sym ((40, 41), "x"));
                (PSym ((76, 77), "y"), Sym ((78, 79), "y"))])))
  ; ( "Undeepen"
    , (undeepen (0, [])
         [([Sym ((0, 0), "x"); Sym ((0, 0),"y")], Sym ((0, 0),"x"));
          ([Sym ((0, 0),"a"); Sym ((0, 0),"b")], Sym ((0, 0),"a"))])
      = ((0, []),
         Lam ((0, 1),
              [(PSym ((0, 0), "x"),
                Lam ((0, 1), [(PSym ((0, 0), "y"), Sym ((0, 0), "x"))]));
               (PSym ((0, 0), "a"),
                Lam ((0, 1), [(PSym ((0, 0), "b"), Sym ((0, 0), "a"))]))])))
  ; ( "Deep lambda"
    , deep_lambda symbol (0, (Util.char_list "(λ [x y] x)"))
      = Ok
          ((12, []),
           Lam ((12, 13),
                [(PSym ((5, 6), "x"),
                  Lam ((12, 13)
                      ,[(PSym ((7, 8), "y"), Sym ((10, 11), "x"))]))])))]

let tunit (source: source): Type.Type.t parseresult =
  (map (andThen
          (literal "<")
          (literal ">"))
     (Util.take_ok
        (fun ((end_pos, rest), ((), ()))
         -> ((end_pos, rest)
            ,Type.tUnit))))
    source

let tunit_tests =
  [("AbsoluT ENHET"
   ,tunit (0
          ,['<'; '>'])
    = Ok ((2,[])
         ,Type.tUnit))]

let ttuple (typ: source -> Type.Type.t parseresult) source: Type.Type.t parseresult =
  (map (andThen (andThen (literal "<")
                   (n_or_more 1 typ))
          (literal ">"))
     (Util.take_ok
        (fun ((end_pos, rest)
             ,(((), members), ())) ->
          ((end_pos, rest), (Type.tTuple members)))))
    source

let ttuple_tests =
  [("ttuple ttuple ttuple"
   , ttuple tunit (0, (Util.char_list "< <>  <> > ]"))
     = Ok ((9, [' ';']'])
          ,Type.tTuple [Type.tUnit; Type.tUnit]))]

let tarrow (typ: source -> Type.Type.t parseresult) source : Type.Type.t parseresult =
  (map (andThen (andThen (andThen
                            (literal "(")
                            (literal "->"))
                   (n_or_more 2 typ))
          (literal ")"))
     (Util.take_ok (fun ((end_pos, rest)
                        ,((((), ()), the_types), ())) ->
          let rec arrowise = function
            | t :: [] -> t
            | t :: rest ->
              (Type.tArrow t (arrowise rest))
            | [] -> failwith "arrowise should not get empty input"
          in ((end_pos, rest)
             ,arrowise the_types))))
    source

let tsym global_env source: Type.Type.t parseresult =
  (map (orElse symbol quoted_symbol)
     (function
       | Ok ((rest, index), Sym (_pos, s)) ->
         Ok ((rest, index),
             Type.Type.TyVar
               (let tv = Type.TypeVariable.create global_env in
                tv.name <- s;
                tv))
       | _ -> Error "Not a symbol"))
  source

let tu8: source -> 'a parseresult =
  (map
     (literal "U8")
     (Util.take_ok (fun (state, ()) -> (state, Type.tU8))))

let rec typ global_env src : Type.Type.t parseresult =
  (orElse_list [tarrow (typ global_env)
               ;tunit
               ;tu8
               ;tsym global_env])
    src

let unit source: Expr.expr parseresult =
  (map (andThen (literal "<")
          (literal ">"))
     (Util.take_ok
        (fun ((end_pos, rest), ((), ())) ->
          ((end_pos, rest)
          ,Expr.Unit (fst source, end_pos)))))
    source

let u8 =
  (map
     (andThen
    	(andThen (andThen
    		    (literal "(")
    		    (literal "u8"))
    	   symbol)
    	(literal ")"))
     (function
       | Ok ((src_end_pos, src_rest)
            ,((((), ())
              ,Sym ((sym_start_pos, sym_end_pos), name)), ())) ->
         (match int_of_string_opt name with
          | Some n ->
            Ok ((src_end_pos, src_rest)
               ,Expr.U8 ((sym_start_pos, sym_end_pos)
                   ,n))
          | None -> Error (Util.str ["Failiig to parse u8: "
                                    ;name]))
       | Error e ->
         Error e
       | _ -> failwith "nopez seniorez"))

let tuple
      (expression: source -> Expr.expr parseresult)
      source
    : Expr.expr parseresult =
  (map (andThen (andThen (literal "<")
                   (n_or_more 1 expression))
          (literal ">"))
     (Util.take_ok
        (fun ((end_pos, rest), (((), children),())) ->
          ((end_pos, rest)
          ,Expr.Tuple ((fst source, end_pos), children)))))
    source

let annotation gensym_env (expression: source -> Expr.expr parseresult) source : Expr.expr parseresult =
  (map (andThen (andThen (andThen (andThen
                                     (literal "(")
                                     (literal ":"))
                            (typ gensym_env))
                   expression)
          (literal ")"))
     (Util.take_ok (fun ((end_pos, rest), (((((), ()), t), e), ())) ->
          ((end_pos, rest)
          ,Expr.Ann ((fst source, end_pos), t, e)))))
    source

(* Since this would match many things, ensure it's last in the orElse sequence *)
let application
      (expression: source -> Expr.expr parseresult) source : Expr.expr parseresult =
  (map (andThen (andThen
                   (literal "(")
                   (n_or_more 2 expression))
          (literal ")"))
     (* PRETTY GOOD *)
     (Util.take_ok (fun ((pos, rest), (((), xs), ())) ->
          (* Forgive me *)
          let rec appise = function
            | x :: [] -> x
            | x :: xs -> Expr.App ((fst source, pos)
                             ,appise xs
                             ,x)
            | [] -> failwith "Go app yourself"
          in ((pos, rest)
             ,appise (List.rev xs)))))
    source

let let_expr expression source: Expr.expr parseresult =
  (map
     (andThen
	(andThen
	   (andThen
	      (andThen
		 (literal "(")
		 (literal "let"))
	      (andThen
		 (pattern expression)
		 expression))
	   expression)
	(literal ")"))
     (Util.take_ok
        (function
         | ((end_index, rest)
           ,(((((), ()),
               (Expr.PSym (_psym_pos, name), definition)),
              body),
             ())) ->
            ((end_index, rest)
            ,Expr.Let ((fst source, end_index), name, definition, body))
         | _ -> failwith "let_expr with non-PSym definition - fix this")))
  source

let dict expression source =
  (map (andThen
	  (andThen (literal "{")
	     (n_or_more 0 (andThen expression expression)))
	  (literal "}"))
     (Util.take_ok
	(fun ((pos, rest), (((), keys_and_vals), ())) ->
	  ((pos, rest)
          ,Expr.Dict ((fst source, pos), keys_and_vals)))))
    source

let match_expr expression source =
  (map (andThen
      (andThen
         (andThen
            (andThen
               (literal "(")
               (literal "match"))
            expression)
         (n_or_more 1 (andThen
                         (pattern expression)
                         expression)))
      (literal ")"))
     (Util.take_ok
        (fun
           ((pos, rest), (((((), ()), expr), expr_pattern_expr_list), ())) ->
          ((pos, rest)
          ,Expr.Match ((fst source, pos), expr, expr_pattern_expr_list)))))
    source

let rec expression gensym_env (source_code: source): Expr.expr parseresult =
  let expression = expression gensym_env in
  orElse_list
    [ u8
    ; tuple expression
    ; unit
    ; string
    ; quoted_symbol
    ; symbol
    ; vector expression
    ; dict expression
    ; set expression
    ; lambda expression
    ; deep_lambda expression
    ; annotation gensym_env expression
    ; let_expr expression
    (* ; tagged_expr expression *)
    ; match_expr expression
    ; application expression]
    source_code

let negpos = (-1, -1)

let comp f g x = f (g x)

let string_of_quoted_symbol s = Util.str ["\""; s; "\""]

let expression_tests =
  [ ( "Why does this symbol not end at the space?"
    , expression (Type.new_gensym_state ()) (0, (Util.char_list "hello#{}#"))
      = Ok ((5,['#'; '{'; '}'; '#'])
           ,Sym ((0, 5), "hello")))
  ; ( "Set of stuff"
    , expression (Type.new_gensym_state ()) (0, (Util.char_list "#{ hello there}#"))
      = Ok ((16, []),
            Set ((0, 16), [Sym ((3, 8), "hello"); Sym ((9, 14), "there")])))
  ; ( "Set of vector"
    , expression (Type.new_gensym_state ()) (0, (Util.char_list "#{ []}# "))
      = Ok ((7, [' ']), Set ((0, 7), [Vector ((2, 5), [])])))
  ; ( "Unit"
    , expression (Type.new_gensym_state ()) (0, (Util.char_list "  <> "))
      = Ok ((4, [' ']), Unit (0, 4)))
  ; ( "Full tuple"
    , expression (Type.new_gensym_state ()) (0, Util.char_list "<hello <>> ")
      = Ok ((10, [' '])
           ,Tuple ((0, 10), [Sym ((1, 6), "hello"); Unit (6, 9)])))
  ; ("parse K"
    , expression (Type.new_gensym_state ()) (0, Util.char_list "(λ x (λ y x))")
      = Ok
          ((15, []),
           Lam ((0, 15),
                [(PSym ((4, 5), "x"),
                  Lam ((5, 14), [(PSym ((10, 11), "y"), Sym ((12, 13), "x"))]))])))
  ; ("Annotate Unit"
    , expression (Type.new_gensym_state ()) (0, Util.char_list "(: <> <>)")
      = Ok ((9, [])
           ,Ann ((0, 9)
                ,Type.tUnit
                ,Unit (5, 8))))
  ; ("Deep λ"
    , expression (Type.new_gensym_state ()) (0, Util.char_list "(λ [x y] x)")
      = Ok ((12, []),
            Lam ((12, 13),
                 [(PSym ((5, 6), "x"),
                   Lam ((12, 13), [(PSym ((7, 8), "y"), Sym ((10, 11), "x"))]))])))
  ; ("Advanced K annotation"
    , expression (Type.new_gensym_state ()) (0, Util.char_list "(: (-> X Y X) (λ [x y] x))")
      = Ok
        ((27, []),
         Ann ((0, 27),
              Type.Type.TyOp
                ("->",
                 [Type.Type.TyVar
                    {Type.TypeVariable.id = 0; name = "X"; instance = None};
                  Type.Type.TyOp
                    ("->",
                     [Type.Type.TyVar
                        {Type.TypeVariable.id = 1; name = "Y"; instance = None};
                      Type.Type.TyVar
                        {Type.TypeVariable.id = 2; name = "X"; instance = None}])]),
              Lam ((26, 27),
                   [(PSym ((19, 20), "x"),
                     Lam ((26, 27), [(PSym ((21, 22), "y"), Sym ((24, 25), "x"))]))]))))
  ; ("Apply annotated K"
    , expression (Type.new_gensym_state ()) (0, Util.char_list "((: (-> X Y X) (λ [x y] x)) 音 '沈黙')")
      = Ok
        ((41, []),
         App ((0, 41),
              App ((0, 41),
                   Ann ((1, 28),
                        Type.Type.TyOp
                          ("->",
                           [Type.Type.TyVar
                              {Type.TypeVariable.id = 0; name = "X"; instance = None};
                            Type.Type.TyOp
                              ("->",
                               [Type.Type.TyVar
                                  {Type.TypeVariable.id = 1; name = "Y"; instance = None};
                                Type.Type.TyVar
                                  {Type.TypeVariable.id = 2; name = "X"; instance = None}])]),
                        Lam ((27, 28),
                             [(PSym ((20, 21), "x"),
                               Lam ((27, 28), [(PSym ((22, 23), "y"), Sym ((25, 26), "x"))]))])),
                   Sym ((29, 32), "音")),
              Sym ((33, 40), "沈黙"))))

  ; ( "FAILURE?? Nested applications happen in order"
    , application (expression (Type.new_gensym_state ())) (0, Util.char_list "(x (y z) (a b) c)")
      = Ok
          ((17, []),
           App ((0, 17),        (* (((x (y z))) (a b) c) *)
                App ((0, 17),
                     App ((0, 17), Sym ((1, 2), "x"),
                          App ((2, 8), Sym ((4, 5), "y"), Sym ((6, 7), "z"))),
                     App ((8, 14), Sym ((10, 11), "a"), Sym ((12, 13), "b"))),
                Sym ((15, 16), "c"))))
  ; ("Strings are parsed as expressions"
    , expression (Type.new_gensym_state ()) (0, Util.char_list "  \"Hello\"  ")
      = Ok ((7, [' '; ' ']), String ((2, 7), "Hello")))
  ; ("Application and typ vars"
    , expression (Type.new_gensym_state ()) (0, Util.char_list "((λ x (λ y x)) \"first\" \"second\")")
      = Ok ((30, []),
            App ((0, 30),
                 App ((0, 30),
                      Lam ((1, 16),
                           [(PSym ((5, 6), "x"),
                             Lam ((6, 15), [(PSym ((11, 12), "y"), Sym ((13, 14), "x"))]))]),
                      String ((17, 22), "first")),
                 String ((23, 29), "second"))))
  ; ("parse u8"
    , expression (Type.new_gensym_state ()) (0, Util.char_list "  (u8 1337)")
      = Ok ((11, [])
           ,U8 ((6, 10), 1337)))
  ; ("You know what they say about men with large vocabularies? They also have a large Dict"
    , dict (expression (Type.new_gensym_state ())) (0, Util.char_list "{\"ichi\" 1 \"ni\" 2 \"san\" 3}")
      = Ok ((19, []),
            Dict ((0, 19),
                  [(String ((1, 5), "ichi"), Sym ((6, 7), "1"));
                   (String ((8, 10), "ni"), Sym ((11, 12), "2"));
                   (String ((13, 16), "san"), Sym ((17, 18), "3"))])))]

let typ_tests =
  [("Longbow arrows"
   , typ
       (Type.new_gensym_state ())
       (0, Util.char_list "(-> X Y X)")
     = Ok
       ((10, []),
        Type.Type.TyOp
          ("->",
           [Type.Type.TyVar
              {Type.TypeVariable.id = 0; name = "X"; instance = None};
            Type.Type.TyOp
              ("->",
               [Type.Type.TyVar
                  {Type.TypeVariable.id = 1; name = "Y"; instance = None};
                Type.Type.TyVar
                  {Type.TypeVariable.id = 2; name = "X"; instance = None}])])))]


let src_to_src src =
  Util.take_ok
    (Util.comp (Expr.string_of_expr (Type.new_gensym_state ())) Util.second)
    (expression
       (Type.new_gensym_state ())
       (0, (Util.char_list src)))

let src_to_src_test src =
  src_to_src src
  = Ok src

let string_of_expr_tests =
  [("string of quoted symbol"
   ,Expr.string_of_expr
       (Type.new_gensym_state ())
       (Sym ((0, 0), " I'm a quoted symbol"))
    = "\" I'm a quoted symbol\"")
  ;("string of lambda"
   ,src_to_src "(λ x (λ y x))"
    = Ok "(λ x (λ y x))")
  ;("string of app"
   ,let src = "(((λ x (λ y x)) \"first\") \"second\")" in
    src_to_src src
    = Ok src)]

type io_paths =
  { input_files: string list
  ; output_file: string}

type compiler_cmd =
  | ShowPrintTests of Expr.position
  | OutputCToPath of Expr.position * io_paths
  | OutputExeToPath of Expr.position * io_paths
  | PrintHelp of Expr.position
  | PublishAndPrintIDFromSTDIN of Expr.position
  | NoCommandArguments of Expr.position
  | Run of Expr.position * string

let parse_arg_test_results source =
  (map
     (literal "--tests")
     (Util.take_ok (fun ((end_pos, rest), ()) ->
          ((end_pos, rest)
          ,ShowPrintTests (fst source, end_pos)))))
    source

let parse_arg_run source =
  (map (andThen
          (literal "--run")
          symbol_native_string)
     (Util.take_ok (fun ((end_pos, rest), ((), src_path)) ->
          ((end_pos, rest)
          ,Run ((fst source, end_pos), src_path)))))
  source

let parse_output_exe source =
  (map
     (andThen
	(andThen
	   (orElse
              (literal "--output")
              (literal "-o"))
	   symbol_native_string)
	(n_or_more 1 symbol_native_string))
     (function
      | Ok ((_index, _rest), (((), _output_file), [])) ->
         Error "No input files given - add some source file name(s) at the end of the command"
      | Ok ((index, rest), (((), output_file), input_files)) ->
	 Ok ((index, rest)
            ,OutputExeToPath (((fst source)
                              ,index)
                            , { input_files = input_files
			      ; output_file = output_file}))
      | Error e -> Error e))
    source

let parse_output_c source =
  (map
     (andThen
	(andThen
	   (orElse
              (literal "--output-c")
              (literal "-oc"))
	   symbol_native_string)
	(n_or_more 1 symbol_native_string))
     (function
      | Ok ((_index, _rest), (((), _output_file), [])) ->
         Error "No input files given - add some source file name(s) at the end of the command"
      | Ok ((index, rest), (((), output_file), input_files)) ->
	 Ok ((index, rest)
            ,OutputCToPath (((fst source)
                            ,index)
                          , { input_files = input_files
			    ; output_file = output_file}))
      | Error e -> Error e))
    source

let print_help (source: source) =
  (map (orElse_list [(literal "--help")
                    ;(literal "-h")])
     (function
      | Ok ((index, rest), ()) ->
         Ok ((index, rest)
            ,PrintHelp (fst source, index))
      | Error e -> Error e))
    source

let print_welcome source =
  (map (literal "")
     (function
      | Ok ((index, rest), ()) ->
         Ok ((index, rest)
            ,NoCommandArguments (fst source, index))
      | Error e -> Error e))
    source

let parse_publish (source: source) =
  map
    (literal "--publish")
    (function
     | Ok ((index, rest), ()) ->
        Ok ((index, rest), PublishAndPrintIDFromSTDIN (fst source, index))
     | Error e -> Error e)
    source

let parse_args =
  (map
     (andThen
        symbol_native_string       (* the name of the command *)
        (orElse_list [parse_arg_test_results
                     ;parse_output_c
                     ;parse_output_exe
                     ;parse_publish
                     ;parse_arg_run
                     ;print_help
                     ;print_welcome]))
     (Util.take_ok
        (fun ((end_pos, rest), (_, cmd)) ->
          ((end_pos, rest), cmd))))

let parse_args_tests =
  [("Print test results"
   , let src = "platoc --test-results" in
     parse_args (0
                ,(Util.char_list src))
     = let pos = (0, String.length src) in
       Ok ((snd pos, [])
          ,ShowPrintTests pos))
  ;("Output C file"
   , let src = "platoc --output-c myfile.c mysource.plato" in
     parse_args (0
                ,(Util.char_list src))
     = let pos = (0, String.length src) in
       Ok ((snd pos, [])
          ,OutputCToPath (pos, {input_files = ["mysource.plato"]
			       ;output_file = "myfile.c"})))]
