(* Sincere thanks to the author of https://www.cs.cornell.edu/courses/cs3110/2011sp/Lectures/lec26-type-inference/type-inference.htm for sharing their knowledge *)
(* `infer` is a modified version of a MIT Licenced inferrer by Andrea Cognolato, Github user mrandri19 (https://github.com/mrandri19/Wand87-A-Simple-Algorithm-and-Proof-for-Type-Inference). Grazie mille. Used under the MIT license *)

let __gensym_state__: int ref = ref (-1);;
let gensym (): Parser.typ =
  incr __gensym_state__;
  TVar ((-1, -1),!__gensym_state__)

type equation =
  Parser.typ * Parser.typ

(* invariant for substitutions:
   no id on a lhs occurs in any term earlier in the list *)
type substitution =
  (Parser.id * Parser.typ) list

(* check if a variable v occurs in a Parser.typ t *)
let rec occurs (v : Parser.id) (t : Parser.typ) : bool =
  match t with
  | Parser.TVar (_pos, y) ->
     v = y
  | Parser.TSym (pos, _y) ->
     failwith (Util.str ["Can't do textual symbols just yet - the type `id` should be a union. Error at position: "
                        ;Parser.string_of_position pos])
  | Parser.TTerm (_pos, _, s) ->
     List.exists
       (occurs v)
       s
  | Parser.TVector (_pos, s) ->
     (occurs v s)
  | Parser.TSet (_pos, s) ->
     (occurs v s)
  | Parser.TTuple (_pos, s) ->
     List.exists
       (occurs v)
       s
  | Parser.TDict (_pos, _key_typ, _value_typ) ->
     failwith "I do not yet understand what occurs should do in a TDict"
  | Parser.TArrow (_pos, input, output) ->
     List.exists
       (occurs v)
       [input; output]
  | Parser.TUnit _pos -> false
  | Parser.TU8 _pos -> false
  | Parser.TString _pos -> false

(* substitute Parser.typ s for all occurrences of variable v in Parser.typ t *)
let rec subst (s : Parser.typ) (v : Parser.id) (t : Parser.typ) : Parser.typ =
  match t with
  | Parser.TVar (_pos, y) ->
     if v = y
     then s
     else t
  | Parser.TSym (_pos, _y) ->
     failwith "Yeah this ain't gonna happen"
  | Parser.TTerm (pos, f, u) ->
     Parser.TTerm (pos, f, List.map (subst s v) u)
  | Parser.TVector (_pos, u) ->
     Parser.TVector (_pos, subst s v u)
  | Parser.TSet (_pos, u) ->
     Parser.TSet (_pos, subst s v u)
  | Parser.TDict (_pos, _key_typ, _value_typ) ->
     failwith "subst for TDict - I do not yet understand this"
  | Parser.TTuple (_pos, u) ->
     Parser.TTuple (_pos, List.map (subst s v) u)
  | Parser.TArrow (_pos, input, output) ->
     Parser.TArrow (_pos, subst s v input, (subst s v output))
  | Parser.TUnit _pos -> Parser.TUnit _pos
  | Parser.TU8 _pos -> Parser.TU8 _pos
  | Parser.TString _pos -> Parser.TString _pos

(* apply a substitution righ to left *)
let apply (s : substitution) (t : Parser.typ) : Parser.typ =
  List.fold_right (fun (x, u) -> subst u x) s t

(* unify one pair  *)
let rec unify_one (s : Parser.typ) (t : Parser.typ) : substitution =
  (* a substitution is a list of id * typ
It describes the typ that should be inserted in place of the id *)
  match (s, t) with
  | (Parser.TVar (_posl, x), Parser.TVar (_posr, y)) ->
     if x = y
     then []
     else [(x, t)]
  | (Parser.TUnit _pos
    ,(Parser.TUnit __pos
      | Parser.TString __pos
     | Parser.TU8 __pos)) ->
     []
  | (Parser.TU8 _u8pos, (Parser.TUnit _pos | Parser.TString _pos | Parser.TU8 _pos)) ->
     []
  | (Parser.TString _posl, (Parser.TString _posr | Parser.TUnit _posr | Parser.TU8 _posr)) ->
     []
  | (Parser.TVar (_posl, x), Parser.TUnit posr) ->
     [(x, Parser.TUnit posr)]
  | (Parser.TVar (_posl, x), Parser.TString posr) ->
     [x, Parser.TString posr]
  | (Parser.TVar (_posl, x), Parser.TU8 posr) ->
     [x, Parser.TU8 posr]
  | (Parser.TUnit posl, Parser.TVar (_posr, x)) ->
     [(x, Parser.TUnit posl)]
  | (Parser.TU8 posl, Parser.TVar (_posr, x)) ->
     [(x, Parser.TU8 posl)]
  | (Parser.TString posl, Parser.TVar (_posr, x)) ->
     [(x, Parser.TString posl)]
  | (Parser.TTerm (_posl, _f, _sc)
    ,(Parser.TUnit _posr | Parser.TString _posr | Parser.TU8 _posr)) ->
     failwith "Not unifiable: Head symbol conflict in (Parser.TTerm (f, sc), TParser.TUnit (g))"
  | (Parser.TVector (_posl, _sc)
    , (Parser.TUnit _posr | Parser.TString _posr | Parser.TArrow (_posr, _, _) | Parser.TU8 _posr)) ->
     failwith "Not unifiable: Head symbol conflict in (Parser.TVector (f, sc), TParser.TUnit (g))"
  | (Parser.TVector (_posl, sc), Parser.TVector (_posr, tc)) ->
     unify [(sc, tc)]
  | (Parser.TSet (_posl, _sc), (Parser.TUnit _posr | Parser.TString _posr | Parser.TU8 _posr)) ->
     failwith "Not unifiable: Head symbol conflict in (Parser.TSet (f, sc), TParser.TUnit (g))"
  | (Parser.TTuple (_posl, _sc)
    ,(Parser.TUnit _posr | Parser.TString _posr | Parser.TU8 _posr)) ->
     failwith "Not unifiable: Head symbol conflict in (Parser.TTuple (f, sc), Parser.TUnit)"
  | (Parser.TArrow (_posl, _input, _output)
    ,(Parser.TUnit _posr | Parser.TString _posr | Parser.TU8 _posr)) ->
     failwith "Not unifiable: Head symbol conflict in (Parser.TArrow (input, output), TParser.TUnit)"
  | ((Parser.TUnit _posl | Parser.TU8 _posl | Parser.TString _posl)
    , Parser.TTerm (_posr, _g, [])) ->
     []
  | ((Parser.TUnit _posl | Parser.TString _posl | Parser.TU8 _posl)
    , Parser.TTerm (_posr, _g, _tc)) ->
     failwith "Not unifiable: TParser.TUnit Head symbol conflict in (TParser.TUnit (f), Parser.TTerm (g, tc))"
  | ((Parser.TUnit _posl | Parser.TString _posl | Parser.TU8 _posl)
    , (Parser.TVector (_posr, _tc) | Parser.TSet (_posr, _tc))) ->
     failwith "Not unifiable: TParser.TUnit Head symbol conflict in (TParser.TUnit (f), Parser.TVector (g, tc))"
  | ((Parser.TUnit _posl | Parser.TString _posl | Parser.TU8 _posl)
    , Parser.TTuple (_posr, [])) ->
     []
  | ((Parser.TUnit _posl | Parser.TString _posl | Parser.TU8 _posl)
    , Parser.TTuple (_posr, _tc)) ->
     failwith "Not unifiable: TParser.TUnit Head symbol conflict in ((Parser.TUnit | Parser.TString | Parser.TU8), Parser.TTuple tc)"
  | ((Parser.TUnit _posl | Parser.TString _posl | Parser.TU8 _posl)
    , Parser.TArrow (_posr, _input, _output)) ->
     failwith "Not unifiable: TParser.TUnit Head symbol conflict in (Parser.TUnit, Parser.TArrow (input, output))"
  | (Parser.TTerm (_posl, _f, _sc)
    ,Parser.TArrow (_posr, _input, _output)) ->
     failwith "Not unifiable: Parser.TArrow is not Head, symbol conflict"
  | (Parser.TTerm (_posl, f, sc)
    , Parser.TTerm (_posr, g, tc)) -> (* Parser.TTerm * Parser.TTerm *)
     if f = g && List.length sc = List.length tc
     then unify (List.combine sc tc)
     else failwith "Not unifiable: Head symbol conflict"
  | ((Parser.TVector (_posl, _sc) | Parser.TSet (_posl, _sc))
    ,Parser.TTerm (_posr, _g, _tc)) ->
     failwith "Not unifiable: Head symbol conflict"
  | (Parser.TTerm (_posl, _f, _sc)
    , (Parser.TVector (_posr, _tc) | Parser.TSet (_posr, _tc))) ->
     failwith "Not unifiable: Head symbol conflict"
  | (Parser.TTuple (_posl, _sc)
    , Parser.TTerm (_posr, _f, _tc))
    | (Parser.TTerm (_posl, _f, _sc), Parser.TTuple (_posr, _tc)) ->
     failwith "Not unifiable: Head symbol conflict"
  | (Parser.TArrow (_posl, _input, _output)
    ,Parser.TTerm (_posr, _g, _tc)) ->
     failwith "Not unifiable: Parser.TArrow and Parser.TTerm Head symbol conflict"
  | (Parser.TVar (_posl, x)
    ,(Parser.TTerm (_posr, _, _) as t))
    | ((Parser.TTerm (_posl, _,_) as t),
       Parser.TVar (_posr, x)) ->
     if occurs x t
     then failwith "not unifiable: ciruclarity in (Parser.TVar x, (Parser.TTerm (_, _) as t))"
     else [(x, t)]
  | (Parser.TSet _, Parser.TVector _) | (Parser.TVector _, Parser.TSet _) | (Parser.TTuple _, Parser.TVector _) | (Parser.TVector _, Parser.TTuple _) ->
     failwith "Not unifiable: Head symbol conflict"
  | (Parser.TArrow (_posl, _input, _output), Parser.TVector (_posr, _tc)) ->
     failwith "Not unifiable: Parser.TArrow and Parser.TVector Head symbol conflict"
  | (Parser.TVar (_posl, x), (Parser.TVector (_posr, _) as v))
    | ((Parser.TVector (_posl, _) as v), Parser.TVar (_posr, x)) ->
     if occurs x v
     then failwith "not unifiable: ciruclarity in (Parser.TVar x, (Parser.TVector (_, _) as t))"
     else [(x, v)]
  | (Parser.TSet (_posl, _sc)
    ,Parser.TArrow (_posr, _input, _output)) ->
     failwith "Not unifiable: Parser.TArrow is not Head, symbol conflict"
  | (Parser.TSet (_posl, sc), Parser.TSet (_posr, tc)) ->
     unify [(sc, tc)]
  | (Parser.TTuple _, Parser.TSet _) | (Parser.TSet _, Parser.TTuple _) ->
     failwith "Not unifiable: Head symbol conflict"
  | (Parser.TArrow (_posl, _input, _output)
    ,Parser.TSet (_posr, _tc)) ->
     failwith "Not unifiable: Parser.TArrow and Parser.TSet Head symbol conflict"
  | (Parser.TVar (_pos_var, x)
    ,Parser.TSet (pos_set, t))
    | (Parser.TSet (pos_set, t)
      , Parser.TVar (_pos_var, x)) ->
     if occurs x (Parser.TSet (pos_set, t))
     then failwith "not unifiable: ciruclarity in (Parser.TVar x, (Parser.TSet (_, _) as t))"
     else [(x, (Parser.TSet (pos_set, t)))] (* is this correct?  *)
  | (Parser.TTuple (_posl, _sc)
    ,Parser.TArrow (_posr, _input, _output)) ->
     failwith "Not unifiable: Parser.TArrow is not Head, symbol conflict"
  | (Parser.TTuple (_posl, sc), Parser.TTuple (_posr, tc)) ->
     if List.length sc = List.length tc
     then unify (List.combine sc tc)
     else failwith "Not unifiable: Head symbol conflict"
  | (Parser.TArrow (_posl, _input, _output), Parser.TTuple (_posr, _tc)) ->
     failwith "Not unifiable: Parser.TArrow and Parser.TTuple Head symbol conflict"
  | (Parser.TVar (_pos_var, x)
    ,(Parser.TTuple (_pos_tup, _) as t))
    | ((Parser.TTuple (_pos_tup, _) as t)
      ,Parser.TVar (_pos_var, x)) ->
     if occurs x t
     then failwith "not unifiable: ciruclarity in (Parser.TVar x, (Parser.TTuple (_, _) as t))"
     else [(x, t)]
  | (Parser.TArrow (_posl, f_input, f_output), Parser.TArrow (_posr, g_input, g_output)) ->
     unify (List.combine
              [f_input; f_output]
              [g_input; g_output])
  | (Parser.TVar (_pos_var, x), (Parser.TArrow (_pos_arr, _, _) as t))
    | ((Parser.TArrow (_pos_arr, _,_) as t), Parser.TVar (_pos_var, x)) ->
     if occurs x t
     then failwith "not unifiable: ciruclarity in (Parser.TVar x, (Parser.TArrow (_, _) as t))"
     else [(x, t)]
  | (_, Parser.TDict _) -> failwith "COOL TDICT on the right"
  | (TDict (_, _, _),
     (TVar (_, _)|TTerm (_, _, _)|TArrow (_, _, _)|TUnit _|TString _|
      TTuple (_, _)|TVector (_, _)|TSet (_, _)|TU8 _)) -> failwith "COOL TDICT on the left"
  | (TSym (_pos, _s), _) -> failwith "Symbol stuff not done"
  | (_, TSym (_pos, _s)) -> failwith "Symbol stuff not done"

(* unify a list of pairs, i.e. equations *)
and unify (equations : equation list) : substitution =
  match equations with
  | [] -> []
  | (x, y) :: t ->
     let t2 = unify t in
     let t1 = unify_one (apply t2 x) (apply t2 y) in
     t1 @ t2

let negpos = (-1, -1)

let term k v =
  Parser.TTerm (negpos, k, v)

let v s =
  Parser.TVar (negpos, s)

let unify_tests =
  [("Unify: Infer"
   , apply (unify [v 1, (Parser.TTuple (negpos, [(v 5); (v 4)]))
                  ;v 5, Parser.TVector (negpos, (v 7))
													     ;v 4, Parser.TSet (negpos, Parser.TU8 negpos)
													     ;v 6, Parser.TU8 negpos
															   ;v 7, Parser.TU8 negpos
													     ;v 6, v 3
															   ;v 7, v 3
													     ;v 2, Parser.TArrow (negpos, v 1, v 3)])
       (v 2)
     = Parser.TArrow
         (negpos,
          Parser.TTuple (negpos
                       ,[Parser.TVector (negpos, Parser.TU8 negpos)
                        ;Parser.TSet (negpos, Parser.TU8 negpos)])
          ,Parser.TU8 negpos))
  ;("Unify: Infer unit"
   , apply (unify [v 1, v 2
                  ;v 2, Parser.TUnit negpos])
       (v 1)
     = Parser.TUnit negpos)]

let string_of_typ = Util.comp Parser.string_of_char_list Parser.string_of_typ

let string_of_equation = function
  | (ty1, ty2) ->
     string_of_typ ty1
     ^ " = "
     ^ string_of_typ ty2

type env = (string * Parser.typ) list

let empty_env = []

let string_of_env env =
  env
  |> List.map (fun (str,ty) -> str ^ ": " ^ string_of_typ ty)
  |> String.concat ", "

exception InferError of string

(* infer all facts (equations) as possible about an expr *)
let infer (expr: Parser.expr): ((equation list * Parser.typ), string) result =
  let rec infer_rec
            (equations: equation list)
            (goals: (env * Parser.expr * Parser.typ) list)
          : equation list =
    match goals with
    | [] -> equations
    | (env, expr, ty) :: rest_of_goals ->
       (match expr with
        | Parser.Sym (pos_sym, x) ->
           (match List.assoc_opt x env with
            | Some x_from_env ->
               let new_equations = (x_from_env, ty) :: equations in
               infer_rec new_equations rest_of_goals
            | None when x = "Log" ->
               let new_equations = (ty, ty) :: equations in (* Log is just Log *)
               infer_rec new_equations rest_of_goals
            | None -> failwith (Util.str ["Can't infer type of the Sym '"
                                         ;Parser.string_of_char_list
                                            (Parser.string_of_expr expr)
                                         ;"'. pos: "
                                         ;Parser.string_of_position pos_sym]))
        | Parser.App (pos, f, argument) ->
           let input_type = gensym () in
           let new_goals =
             (env, f, Parser.TArrow(pos, input_type, ty))
             :: (env, argument, input_type)
             :: rest_of_goals in
           infer_rec equations new_goals
        | Parser.Lam (pos_lam, (PSym (_pos_sym, x), body) :: _rest) ->
           let input_type = gensym () in
           let output_type = gensym () in
           let new_env = (x, input_type) :: env in
           let new_goals = (new_env, body, output_type) :: rest_of_goals in
           let new_equations = (ty
                               ,Parser.TArrow(pos_lam
                                            ,input_type
                                            ,output_type)) :: equations in
           infer_rec new_equations new_goals
        | Parser.Lam (_pos_lam, (Parser.PTag (_pos_ptag, _name, _child), _body) :: _rest) ->
           raise (InferError "lam with ptag not supported")
        | Parser.Lam (pos, []) -> failwith (Util.str ["A lambda binding nothing makes no sense...pos: "
                                                    ;Parser.string_of_position pos])
        | Parser.Unit pos ->
           let new_equations = (ty, Parser.TUnit pos) :: equations in
           infer_rec new_equations rest_of_goals
        | Parser.U8 (pos, _n) ->
           infer_rec ((ty, Parser.TU8 pos) :: equations) rest_of_goals
        | Parser.String (pos, _s) ->
           let new_equations = (ty, Parser.TString pos) :: equations in
           infer_rec new_equations rest_of_goals
        | Parser.Tuple (_pos, _children) ->
           raise (InferError "Parser.Tuple not implemented")
        | Parser.Vector (_pos, _children) ->
           raise (InferError "Parser.Vector not implemented")
        | Parser.Dict (_pos, _keys_and_vals) ->
           raise (InferError "Parser.Dict not implemented")
        | Parser.Set (_pos, _children) ->
           raise (InferError "Parser.Set not implemented")
        | Parser.Ann (_pos, _given_typ, _expr) ->
           raise (InferError "Parser.Ann not implemented")
       (* | Parser.TaggedExpr (pos_tag
        *                    ,tag_name
        *                    ,tagged_value) ->
        *    let this_typ = Parser.TVar (pos_tag, 1337) in
        *    let tagged_value_typ = Parser.TVar (pos_tag, 1338) in
        *    let new_equations = (ty
        *                        ,this_typ)
        *                        :: equations in
        *    let new_goals = (env, tagged_value, tagged_value_typ) :: rest_of_goals in
        *    infer_rec new_equations new_goals
        * | Parser.Match (pos_match
        *               ,tag
        *               ,((PSym (pos_psym
        *                       ,pattern)
        *                 ,body)
        *                 :: rest_of_cases)) ->
        *    let body_ty = gensym () in
        *    let new_equations = (ty, body_ty) :: equations in
        *    let new_goals = (env, body, body_ty)
        *                    :: (env, Parser.Match (pos_match
        *                                         ,tag
        *                                         ,rest_of_cases)
        *                        ,ty)
        *                    :: rest_of_goals in
        *    infer_rec new_equations new_goals
        * | Parser.Match (pos_match
        *               ,tag      (\* should be named something like "question" *\)
        *               ,((Parser.PTag (pos_ptag
        *                             ,name
        *                             ,child)
        *                 ,body)
        *                 :: rest_of_cases)) ->
        *    (\* FIXME HERE *\)
        *    failwith "Parser.Match of PTag not implemented"
        * (\* DONE *\)
        * | Parser.Match (match_pos, tag, []) ->
        *    infer_rec equations rest_of_goals *)
       )
  in
  let ty = gensym () in
  try Ok (infer_rec [] [(empty_env, expr, ty)], ty) with
  | InferError e -> Error e

let infer_and_unify expr =
  match infer expr with
  | Ok (equations, typ) ->
     Ok (apply (unify equations) typ)
  | Error e -> Error e

let infer_tests =
  [("Inferring works"
   , (__gensym_state__ := -1;
      infer (Parser.App (negpos
                       ,Parser.Lam (negpos, [PSym (negpos, "x"), Sym (negpos, "x")])
                       ,Parser.Lam (negpos, [PSym (negpos, "y"), Sym (negpos, "y")]))))
     = Ok ([(Parser.TVar (negpos, 4), Parser.TVar (negpos, 5));
            (Parser.TVar (negpos, 1), Parser.TArrow (negpos
                                               ,Parser.TVar (negpos, 4)
                                               ,Parser.TVar (negpos, 5)));
         (Parser.TVar (negpos, 2), Parser.TVar (negpos, 3));
         (Parser.TArrow (negpos, Parser.TVar (negpos, 1), Parser.TVar (negpos, 0)),
          Parser.TArrow (negpos, Parser.TVar (negpos, 2), Parser.TVar (negpos, 3)))],
        Parser.TVar (negpos, 0)))
  ;("Type of k"
   , (__gensym_state__ := -1;
      infer_and_unify (Parser.Lam (negpos, [PSym (negpos, "x")
                                          ,Parser.Lam (negpos
                                                     ,[PSym (negpos, "y")
                                                      ,Sym (negpos, "x")])])))
     = Ok (Parser.TArrow (negpos
                        ,Parser.TVar (negpos, 4)
                        ,Parser.TArrow (negpos
                                  ,Parser.TVar (negpos, 3)
                                  ,Parser.TVar (negpos, 4)))))
  ; ("Type of Tuple",
     (__gensym_state__ := -1;
      infer_and_unify (Parser.Tuple (negpos
                                   ,[(Parser.U8 (negpos, 1))
                                    ;(Parser.U8 (negpos, 1))]))
      = Ok (Parser.TTuple (negpos, [(TU8 negpos); (TU8 negpos)]))) )
  ; ("Type of Dict"
    ,(__gensym_state__ := -1;
      infer_and_unify (Parser.Dict (negpos
                                  ,[Parser.U8 (negpos, 1)
                                   ,Parser.Lam (negpos, [PSym (negpos, "x"), Sym (negpos, "x")])]))
      = Ok (Parser.TDict (negpos
                        ,TU8 negpos
                        ,TArrow (negpos
                            ,TU8 negpos
                            ,TU8 negpos)))))
   (* ;("match a union"
    *  , (__gensym_state__ := -1;
    *     infer_and_unify (Parser.Match ((0, 83)
    *                                  ,TaggedExpr ((8, 12)
    *                                              ,"Some"
    *                                              ,U8 ((17, 21), 1337))
    *                                  ,[(PTag ((43, 47), "Some", Sym ((48, 49), "n"))
    *                                    ,Sym ((51, 52), "n"));
    *
    *                                    (PSym ((71, 75), "None")
    *                                    ,U8 ((80, 81), 0))]))
    *     = Parser.TU8 negpos)) *)
   (* ;("infer (Some value)"
    *  , (__gensym_state__ := -1;
    *     (\* let option = Parser.TUnion (negpos
    *      *                           ,"a"
    *      *                           ,["Some", Parser.TVar (negpos, 123456)
    *      *                            ;"None", Parser.TUnit negpos]) in *\)
    *     infer_and_unify (Parser.TaggedExpr (negpos
    *                                       ,"Some"
    *                                       ,Parser.U8 (negpos, 1337)))
    *     = Parser.TVar ((-1, -1), 1337)
    *  (\* = Parser.TUnion (negpos
    *   *                ,"a"
    *      *                ,[("Some", Parser.TU8 negpos)
    *      *                 ;("None", Parser.TUnit negpos)]) *\)))
    * ;("infer None"
    *  , (__gensym_state__ := -1;
    *     (\* let option = Parser.TUnion (negpos,
    *      *                            "a"
    *      *                            ,["Some", Parser.TVar (negpos, 123456)
    *      *                             ;"None", Parser.TUnit negpos]) in *\)
    *     infer_and_unify (Parser.TaggedExpr (negpos
    *                                       ,"None", Parser.U8 (negpos, 1337)))
    *     = Parser.TVar ((-1, -1), 1337) (\* = option *\))) *)]
