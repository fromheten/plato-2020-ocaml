(* Sincere thanks to the author of https://www.cs.cornell.edu/courses/cs3110/2011sp/Lectures/lec26-type-inference/type-inference.htm for sharing their knowledge *)
(* `infer` is a modified version of a MIT Licenced inferrer by Andrea Cognolato, Github user mrandri19 (https://github.com/mrandri19/Wand87-A-Simple-Algorithm-and-Proof-for-Type-Inference). Grazie mille. Used under the MIT license *)

let __gensym_state__: int ref = ref (-1);;
let gensym (): Parse.typ =
  incr __gensym_state__;
  TVar ((-1, -1),!__gensym_state__)

type equation =
  Parse.typ * Parse.typ

(* invariant for substitutions:
   no id on a lhs occurs in any term earlier in the list *)
type substitution =
  (Parse.id * Parse.typ) list

(* check if a variable v occurs in a Parse.typ t *)
let rec occurs (v : Parse.id) (t : Parse.typ) : bool =
  match t with
  | Parse.TVar (pos, y) ->
     v = y
  | Parse.TSym (pos, y) ->
     failwith (Util.str ["Can't do textual symbols just yet - the type `id` should be a union. Error at position: "
                        ;Parse.string_of_position pos])
  | Parse.TTerm (pos, _, s) ->
     List.exists
       (occurs v)
       s
  | Parse.TVector (pos, s) ->
     (occurs v s)
  | Parse.TSet (pos, s) ->
     (occurs v s)
  | Parse.TTuple (pos, s) ->
     List.exists
       (occurs v)
       s
  | Parse.TDict (pos, key_typ, value_typ) ->
     failwith "I do not yet understand what occurs should do in a TDict"
  | Parse.TArrow (pos, input, output) ->
     List.exists
       (occurs v)
       [input; output]
  | Parse.TUnit pos -> false
  | Parse.TU8 pos -> false
  | Parse.TString pos -> false

(* substitute Parse.typ s for all occurrences of variable v in Parse.typ t *)
let rec subst (s : Parse.typ) (v : Parse.id) (t : Parse.typ) : Parse.typ =
  match t with
  | Parse.TVar (pos, y) ->
     if v = y
     then s
     else t
  | Parse.TSym (pos, y) ->
     failwith "Yeah this ain't gonna happen"
  | Parse.TTerm (pos, f, u) ->
     Parse.TTerm (pos, f, List.map (subst s v) u)
  | Parse.TVector (_pos, u) ->
     Parse.TVector (_pos, subst s v u)
  | Parse.TSet (_pos, u) ->
     Parse.TSet (_pos, subst s v u)
  | Parse.TDict (_pos, key_typ, value_typ) ->
     failwith "subst for TDict - I do not yet understand this"
  | Parse.TTuple (_pos, u) ->
     Parse.TTuple (_pos, List.map (subst s v) u)
  | Parse.TArrow (_pos, input, output) ->
     Parse.TArrow (_pos, subst s v input, (subst s v output))
  | Parse.TUnit _pos -> Parse.TUnit _pos
  | Parse.TU8 _pos -> Parse.TU8 _pos
  | Parse.TString _pos -> Parse.TString _pos

(* apply a substitution righ to left *)
let apply (s : substitution) (t : Parse.typ) : Parse.typ =
  List.fold_right (fun (x, u) -> subst u x) s t

(* unify one pair  *)
let rec unify_one (s : Parse.typ) (t : Parse.typ) : substitution =
  (* a substitution is a list of id * typ
It describes the typ that should be inserted in place of the id *)
  match (s, t) with
  | (Parse.TVar (_posl, x), Parse.TVar (_posr, y)) ->
     if x = y
     then []
     else [(x, t)]
  | (Parse.TUnit _pos
    ,(Parse.TUnit __pos
      | Parse.TString __pos
     | Parse.TU8 __pos)) ->
     []
  | (Parse.TU8 _u8pos, (Parse.TUnit _pos | Parse.TString _pos | Parse.TU8 _pos)) ->
     []
  | (Parse.TString _posl, (Parse.TString _posr | Parse.TUnit _posr | Parse.TU8 _posr)) ->
     []
  | (Parse.TVar (_posl, x), Parse.TUnit posr) ->
     [(x, Parse.TUnit posr)]
  | (Parse.TVar (_posl, x), Parse.TString posr) ->
     [x, Parse.TString posr]
  | (Parse.TVar (_posl, x), Parse.TU8 posr) ->
     [x, Parse.TU8 posr]
  | (Parse.TUnit posl, Parse.TVar (posr, x)) ->
     [(x, Parse.TUnit posl)]
  | (Parse.TU8 posl, Parse.TVar (posr, x)) ->
     [(x, Parse.TU8 posl)]
  | (Parse.TString posl, Parse.TVar (posr, x)) ->
     [(x, Parse.TString posl)]
  | (Parse.TTerm (posl, f, sc)
    ,(Parse.TUnit posr | Parse.TString posr | Parse.TU8 posr)) ->
     failwith "Not unifiable: Head symbol conflict in (Parse.TTerm (f, sc), TParse.TUnit (g))"
  | (Parse.TVector (posl, sc)
    , (Parse.TUnit posr | Parse.TString posr | Parse.TArrow (posr, _, _) | Parse.TU8 posr)) ->
     failwith "Not unifiable: Head symbol conflict in (Parse.TVector (f, sc), TParse.TUnit (g))"
  | (Parse.TVector (posl, sc), Parse.TVector (posr, tc)) ->
     unify [(sc, tc)]
  | (Parse.TSet (posl, sc), (Parse.TUnit posr | Parse.TString posr | Parse.TU8 posr)) ->
     failwith "Not unifiable: Head symbol conflict in (Parse.TSet (f, sc), TParse.TUnit (g))"
  | (Parse.TTuple (posl, sc)
    ,(Parse.TUnit posr | Parse.TString posr | Parse.TU8 posr)) ->
     failwith "Not unifiable: Head symbol conflict in (Parse.TTuple (f, sc), Parse.TUnit)"
  | (Parse.TArrow (posl, input, output)
    ,(Parse.TUnit posr | Parse.TString posr | Parse.TU8 posr)) ->
     failwith "Not unifiable: Head symbol conflict in (Parse.TArrow (input, output), TParse.TUnit)"
  | ((Parse.TUnit posl | Parse.TU8 posl | Parse.TString posl)
    , Parse.TTerm (posr, g, [])) ->
     []
  | ((Parse.TUnit posl | Parse.TString posl | Parse.TU8 posl)
    , Parse.TTerm (posr, g, tc)) ->
     failwith "Not unifiable: TParse.TUnit Head symbol conflict in (TParse.TUnit (f), Parse.TTerm (g, tc))"
  | ((Parse.TUnit posl | Parse.TString posl | Parse.TU8 posl)
    , (Parse.TVector (posr, tc) | Parse.TSet (posr, tc))) ->
     failwith "Not unifiable: TParse.TUnit Head symbol conflict in (TParse.TUnit (f), Parse.TVector (g, tc))"
  | ((Parse.TUnit posl | Parse.TString posl | Parse.TU8 posl)
    , Parse.TTuple (posr, [])) ->
     []
  | ((Parse.TUnit posl | Parse.TString posl | Parse.TU8 posl)
    , Parse.TTuple (posr, tc)) ->
     failwith "Not unifiable: TParse.TUnit Head symbol conflict in ((Parse.TUnit | Parse.TString | Parse.TU8), Parse.TTuple tc)"
  | ((Parse.TUnit posl | Parse.TString posl | Parse.TU8 posl)
    , Parse.TArrow (posr, input, output)) ->
     failwith "Not unifiable: TParse.TUnit Head symbol conflict in (Parse.TUnit, Parse.TArrow (input, output))"
  | (Parse.TTerm (posl, f, sc)
    ,Parse.TArrow (posr, input, output)) ->
     failwith "Not unifiable: Parse.TArrow is not Head, symbol conflict"
  | (Parse.TTerm (posl, f, sc)
    , Parse.TTerm (posr, g, tc)) -> (* Parse.TTerm * Parse.TTerm *)
     if f = g && List.length sc = List.length tc
     then unify (List.combine sc tc)
     else failwith "Not unifiable: Head symbol conflict"
  | ((Parse.TVector (posl, sc) | Parse.TSet (posl, sc))
    ,Parse.TTerm (posr, g, tc)) ->
     failwith "Not unifiable: Head symbol conflict"
  | (Parse.TTerm (posl, f, sc)
    , (Parse.TVector (posr, tc) | Parse.TSet (posr, tc))) ->
     failwith "Not unifiable: Head symbol conflict"
  | (Parse.TTuple (posl, sc)
    , Parse.TTerm (posr, f, tc))
    | (Parse.TTerm (posl, f, sc), Parse.TTuple (posr, tc)) ->
     failwith "Not unifiable: Head symbol conflict"
  | (Parse.TArrow (posl, input, output)
    ,Parse.TTerm (posr, g, tc)) ->
     failwith "Not unifiable: Parse.TArrow and Parse.TTerm Head symbol conflict"
  | (Parse.TVar (posl, x)
    ,(Parse.TTerm (posr, _, _) as t))
    | ((Parse.TTerm (posl, _,_) as t), Parse.TVar (posr, x)) ->
     if occurs x t
     then failwith "not unifiable: ciruclarity in (Parse.TVar x, (Parse.TTerm (_, _) as t))"
     else [(x, t)]
  | (Parse.TSet _, Parse.TVector _) | (Parse.TVector _, Parse.TSet _) | (Parse.TTuple _, Parse.TVector _) | (Parse.TVector _, Parse.TTuple _) ->
     failwith "Not unifiable: Head symbol conflict"
  | (Parse.TArrow (posl, input, output), Parse.TVector (posr, tc)) ->
     failwith "Not unifiable: Parse.TArrow and Parse.TVector Head symbol conflict"
  | (Parse.TVar (posl, x), (Parse.TVector (posr, _) as v))
    | ((Parse.TVector (posl, _) as v), Parse.TVar (posr, x)) ->
     if occurs x v
     then failwith "not unifiable: ciruclarity in (Parse.TVar x, (Parse.TVector (_, _) as t))"
     else [(x, v)]
  | (Parse.TSet (posl, sc)
    ,Parse.TArrow (posr, input, output)) ->
     failwith "Not unifiable: Parse.TArrow is not Head, symbol conflict"
  | (Parse.TSet (posl, sc), Parse.TSet (posr, tc)) ->
     unify [(sc, tc)]
  | (Parse.TTuple _, Parse.TSet _) | (Parse.TSet _, Parse.TTuple _) ->
     failwith "Not unifiable: Head symbol conflict"
  | (Parse.TArrow (posl, input, output)
    ,Parse.TSet (posr, tc)) ->
     failwith "Not unifiable: Parse.TArrow and Parse.TSet Head symbol conflict"
  | (Parse.TVar (pos_var, x)
    ,Parse.TSet (pos_set, t))
    | (Parse.TSet (pos_set, t)
      , Parse.TVar (pos_var, x)) ->
     if occurs x (Parse.TSet (pos_set, t))
     then failwith "not unifiable: ciruclarity in (Parse.TVar x, (Parse.TSet (_, _) as t))"
     else [(x, (Parse.TSet (pos_set, t)))] (* is this correct?  *)
  | (Parse.TTuple (posl, sc)
    ,Parse.TArrow (posr, input, output)) ->
     failwith "Not unifiable: Parse.TArrow is not Head, symbol conflict"
  | (Parse.TTuple (posl, sc), Parse.TTuple (posr, tc)) ->
     if List.length sc = List.length tc
     then unify (List.combine sc tc)
     else failwith "Not unifiable: Head symbol conflict"
  | (Parse.TArrow (posl, input, output), Parse.TTuple (posr, tc)) ->
     failwith "Not unifiable: Parse.TArrow and Parse.TTuple Head symbol conflict"
  | (Parse.TVar (pos_var, x)
    ,(Parse.TTuple (pos_tup, _) as t))
    | ((Parse.TTuple (pos_tup, _) as t)
      ,Parse.TVar (pos_var, x)) ->
     if occurs x t
     then failwith "not unifiable: ciruclarity in (Parse.TVar x, (Parse.TTuple (_, _) as t))"
     else [(x, t)]
  | (Parse.TArrow (posl, f_input, f_output), Parse.TArrow (posr, g_input, g_output)) ->
     unify (List.combine
              [f_input; f_output]
              [g_input; g_output])
  | (Parse.TVar (pos_var, x), (Parse.TArrow (pos_arr, _, _) as t))
    | ((Parse.TArrow (pos_arr, _,_) as t), Parse.TVar (pos_var, x)) ->
     if occurs x t
     then failwith "not unifiable: ciruclarity in (Parse.TVar x, (Parse.TArrow (_, _) as t))"
     else [(x, t)]
  | (_, Parse.TDict _) -> failwith "COOL TDICT on the right"
  | (TDict (_, _, _),
     (TVar (_, _)|TTerm (_, _, _)|TArrow (_, _, _)|TUnit _|TString _|
      TTuple (_, _)|TVector (_, _)|TSet (_, _)|TU8 _)) -> failwith "COOL TDICT on the left"
  | (TSym (pos, s), _) -> failwith "Symbol stuff not done"
  | (_, TSym (pos, s)) -> failwith "Symbol stuff not done"

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
  Parse.TTerm (negpos, k, v)

let v s =
  Parse.TVar (negpos, s)

let unify_tests =
  [("Unify: Infer"
   , apply (unify [v 1, (Parse.TTuple (negpos, [(v 5); (v 4)]))
                  ;v 5, Parse.TVector (negpos, (v 7))
													     ;v 4, Parse.TSet (negpos, Parse.TU8 negpos)
													     ;v 6, Parse.TU8 negpos
															   ;v 7, Parse.TU8 negpos
													     ;v 6, v 3
															   ;v 7, v 3
													     ;v 2, Parse.TArrow (negpos, v 1, v 3)])
       (v 2)
     = Parse.TArrow
         (negpos,
          Parse.TTuple (negpos
                       ,[Parse.TVector (negpos, Parse.TU8 negpos)
                        ;Parse.TSet (negpos, Parse.TU8 negpos)])
          ,Parse.TU8 negpos))
  ;("Unify: Infer unit"
   , apply (unify [v 1, v 2
                  ;v 2, Parse.TUnit negpos])
       (v 1)
     = Parse.TUnit negpos)]

let string_of_typ = Util.comp Parse.string_of_char_list Parse.string_of_typ

let string_of_equation = function
  | (ty1, ty2) ->
     string_of_typ ty1
     ^ " = "
     ^ string_of_typ ty2

type env = (string * Parse.typ) list

let empty_env = []

let string_of_env env =
  env
  |> List.map (fun (str,ty) -> str ^ ": " ^ string_of_typ ty)
  |> String.concat ", "

exception InferError of string

(* infer all facts (equations) as possible about an expr *)
let infer (expr: Parse.expr): ((equation list * Parse.typ), string) result =
  let rec infer_rec
            (equations: equation list)
            (goals: (env * Parse.expr * Parse.typ) list)
          : equation list =
    match goals with
    | [] -> equations
    | (env, expr, ty) :: rest_of_goals ->
       (match expr with
        | Parse.Sym (pos_sym, x) ->
           (match List.assoc_opt x env with
            | Some x_from_env ->
               let new_equations = (x_from_env, ty) :: equations in
               infer_rec new_equations rest_of_goals
            | None when x = "Log" ->
               let new_equations = (ty, ty) :: equations in (* Log is just Log *)
               infer_rec new_equations rest_of_goals
            | None -> failwith (Util.str ["Can't infer type of the Sym '"
                                         ;Parse.string_of_char_list
                                            (Parse.string_of_expr expr)
                                         ;"'. pos: "
                                         ;Parse.string_of_position pos_sym]))
        | Parse.App (pos, f, argument) ->
           let input_type = gensym () in
           let new_goals =
             (env, f, Parse.TArrow(pos, input_type, ty))
             :: (env, argument, input_type)
             :: rest_of_goals in
           infer_rec equations new_goals
        | Parse.Lam (pos_lam, (PSym (pos_sym, x), body) :: rest) ->
           let input_type = gensym () in
           let output_type = gensym () in
           let new_env = (x, input_type) :: env in
           let new_goals = (new_env, body, output_type) :: rest_of_goals in
           let new_equations = (ty
                               ,Parse.TArrow(pos_lam
                                            ,input_type
                                            ,output_type)) :: equations in
           infer_rec new_equations new_goals
        | Parse.Lam (pos_lam, (Parse.PTag (pos_ptag, name, child), body) :: rest) ->
           raise (InferError "lam with ptag not supported")
        | Parse.Lam (pos, []) -> failwith (Util.str ["A lambda binding nothing makes no sense...pos: "
                                                    ;Parse.string_of_position pos])
        | Parse.Unit pos ->
           let new_equations = (ty, Parse.TUnit pos) :: equations in
           infer_rec new_equations rest_of_goals
        | Parse.U8 (pos, n) ->
           infer_rec ((ty, Parse.TU8 pos) :: equations) rest_of_goals
        | Parse.String (pos, s) ->
           let new_equations = (ty, Parse.TString pos) :: equations in
           infer_rec new_equations rest_of_goals
        | Parse.Tuple (pos, children) ->
           raise (InferError "Parse.Tuple not implemented")
        | Parse.Vector (pos, children) ->
           raise (InferError "Parse.Vector not implemented")
        | Parse.Dict (pos, keys_and_vals) ->
           raise (InferError "Parse.Dict not implemented")
        | Parse.Set (pos, children) ->
           raise (InferError "Parse.Set not implemented")
        | Parse.Ann (pos, given_typ, expr) ->
           raise (InferError "Parse.Ann not implemented")
       (* | Parse.TaggedExpr (pos_tag
        *                    ,tag_name
        *                    ,tagged_value) ->
        *    let this_typ = Parse.TVar (pos_tag, 1337) in
        *    let tagged_value_typ = Parse.TVar (pos_tag, 1338) in
        *    let new_equations = (ty
        *                        ,this_typ)
        *                        :: equations in
        *    let new_goals = (env, tagged_value, tagged_value_typ) :: rest_of_goals in
        *    infer_rec new_equations new_goals
        * | Parse.Match (pos_match
        *               ,tag
        *               ,((PSym (pos_psym
        *                       ,pattern)
        *                 ,body)
        *                 :: rest_of_cases)) ->
        *    let body_ty = gensym () in
        *    let new_equations = (ty, body_ty) :: equations in
        *    let new_goals = (env, body, body_ty)
        *                    :: (env, Parse.Match (pos_match
        *                                         ,tag
        *                                         ,rest_of_cases)
        *                        ,ty)
        *                    :: rest_of_goals in
        *    infer_rec new_equations new_goals
        * | Parse.Match (pos_match
        *               ,tag      (\* should be named something like "question" *\)
        *               ,((Parse.PTag (pos_ptag
        *                             ,name
        *                             ,child)
        *                 ,body)
        *                 :: rest_of_cases)) ->
        *    (\* FIXME HERE *\)
        *    failwith "Parse.Match of PTag not implemented"
        * (\* DONE *\)
        * | Parse.Match (match_pos, tag, []) ->
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
      infer (Parse.App (negpos
                       ,Parse.Lam (negpos, [PSym (negpos, "x"), Sym (negpos, "x")])
                       ,Parse.Lam (negpos, [PSym (negpos, "y"), Sym (negpos, "y")]))))
     = Ok ([(Parse.TVar (negpos, 4), Parse.TVar (negpos, 5));
            (Parse.TVar (negpos, 1), Parse.TArrow (negpos
                                               ,Parse.TVar (negpos, 4)
                                               ,Parse.TVar (negpos, 5)));
         (Parse.TVar (negpos, 2), Parse.TVar (negpos, 3));
         (Parse.TArrow (negpos, Parse.TVar (negpos, 1), Parse.TVar (negpos, 0)),
          Parse.TArrow (negpos, Parse.TVar (negpos, 2), Parse.TVar (negpos, 3)))],
        Parse.TVar (negpos, 0)))
  ;("Type of k"
   , (__gensym_state__ := -1;
      infer_and_unify (Parse.Lam (negpos, [PSym (negpos, "x")
                                          ,Parse.Lam (negpos
                                                     ,[PSym (negpos, "y")
                                                      ,Sym (negpos, "x")])])))
     = Ok (Parse.TArrow (negpos
                        ,Parse.TVar (negpos, 4)
                        ,Parse.TArrow (negpos
                                  ,Parse.TVar (negpos, 3)
                                  ,Parse.TVar (negpos, 4)))))
  ; ("Type of Tuple",
     (__gensym_state__ := -1;
      infer_and_unify (Parse.Tuple (negpos
                                   ,[(Parse.U8 (negpos, 1))
                                    ;(Parse.U8 (negpos, 1))]))
      = Ok (Parse.TTuple (negpos, [(TU8 negpos); (TU8 negpos)]))) )
  ; ("Type of Dict"
    ,(__gensym_state__ := -1;
      infer_and_unify (Parse.Dict (negpos
                                  ,[Parse.U8 (negpos, 1)
                                   ,Parse.Lam (negpos, [PSym (negpos, "x"), Sym (negpos, "x")])]))
      = Ok (Parse.TDict (negpos
                        ,TU8 negpos
                        ,TArrow (negpos
                            ,TU8 negpos
                            ,TU8 negpos)))))
   (* ;("match a union"
    *  , (__gensym_state__ := -1;
    *     infer_and_unify (Parse.Match ((0, 83)
    *                                  ,TaggedExpr ((8, 12)
    *                                              ,"Some"
    *                                              ,U8 ((17, 21), 1337))
    *                                  ,[(PTag ((43, 47), "Some", Sym ((48, 49), "n"))
    *                                    ,Sym ((51, 52), "n"));
    *
    *                                    (PSym ((71, 75), "None")
    *                                    ,U8 ((80, 81), 0))]))
    *     = Parse.TU8 negpos)) *)
   (* ;("infer (Some value)"
    *  , (__gensym_state__ := -1;
    *     (\* let option = Parse.TUnion (negpos
    *      *                           ,"a"
    *      *                           ,["Some", Parse.TVar (negpos, 123456)
    *      *                            ;"None", Parse.TUnit negpos]) in *\)
    *     infer_and_unify (Parse.TaggedExpr (negpos
    *                                       ,"Some"
    *                                       ,Parse.U8 (negpos, 1337)))
    *     = Parse.TVar ((-1, -1), 1337)
    *  (\* = Parse.TUnion (negpos
    *   *                ,"a"
    *      *                ,[("Some", Parse.TU8 negpos)
    *      *                 ;("None", Parse.TUnit negpos)]) *\)))
    * ;("infer None"
    *  , (__gensym_state__ := -1;
    *     (\* let option = Parse.TUnion (negpos,
    *      *                            "a"
    *      *                            ,["Some", Parse.TVar (negpos, 123456)
    *      *                             ;"None", Parse.TUnit negpos]) in *\)
    *     infer_and_unify (Parse.TaggedExpr (negpos
    *                                       ,"None", Parse.U8 (negpos, 1337)))
    *     = Parse.TVar ((-1, -1), 1337) (\* = option *\))) *)]
