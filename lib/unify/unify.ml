(* Sincere thanks to the author of https://www.cs.cornell.edu/courses/cs3110/2011sp/Lectures/lec26-type-inference/type-inference.htm for sharing their knowledge *)
(* `infer` is a modified version of a MIT Licenced inferrer by Andrea Cognolato, Github user mrandri19 (https://github.com/mrandri19/Wand87-A-Simple-Algorithm-and-Proof-for-Type-Inference). Grazie mille. Used under the MIT license *)

let __gensym_state__: int ref = ref (-1);;
let gensym (): Read.typ =
  incr __gensym_state__;
  TVar ((-1, -1),!__gensym_state__)

type equation =
  Read.typ * Read.typ

(* invariant for substitutions:
   no id on a lhs occurs in any term earlier in the list *)
type substitution =
  (Read.id * Read.typ) list

(* check if a variable v occurs in a Read.typ t *)
let rec occurs (v : Read.id) (t : Read.typ) : bool =
  match t with
  | Read.TVar (_pos, y) ->
     v = y
  | Read.TSym (pos, _y) ->
     failwith (Util.str ["Can't do textual symbols just yet - the type `id` should be a union. Error at position: "
                        ;Read.string_of_position pos])
  | Read.TTerm (_pos, _, s) ->
     List.exists
       (occurs v)
       s
  | Read.TVector (_pos, s) ->
     (occurs v s)
  | Read.TSet (_pos, s) ->
     (occurs v s)
  | Read.TTuple (_pos, s) ->
     List.exists
       (occurs v)
       s
  | Read.TDict (_pos, _key_typ, _value_typ) ->
     failwith "I do not yet understand what occurs should do in a TDict"
  | Read.TArrow (_pos, input, output) ->
     List.exists
       (occurs v)
       [input; output]
  | Read.TUnit _pos -> false
  | Read.TU8 _pos -> false
  | Read.TString _pos -> false

(* substitute Read.typ s for all occurrences of variable v in Read.typ t *)
let rec subst (s : Read.typ) (v : Read.id) (t : Read.typ) : Read.typ =
  match t with
  | Read.TVar (_pos, y) ->
     if v = y
     then s
     else t
  | Read.TSym (_pos, _y) ->
     failwith "Yeah this ain't gonna happen"
  | Read.TTerm (pos, f, u) ->
     Read.TTerm (pos, f, List.map (subst s v) u)
  | Read.TVector (_pos, u) ->
     Read.TVector (_pos, subst s v u)
  | Read.TSet (_pos, u) ->
     Read.TSet (_pos, subst s v u)
  | Read.TDict (_pos, _key_typ, _value_typ) ->
     failwith "subst for TDict - I do not yet understand this"
  | Read.TTuple (_pos, u) ->
     Read.TTuple (_pos, List.map (subst s v) u)
  | Read.TArrow (_pos, input, output) ->
     Read.TArrow (_pos, subst s v input, (subst s v output))
  | Read.TUnit _pos -> Read.TUnit _pos
  | Read.TU8 _pos -> Read.TU8 _pos
  | Read.TString _pos -> Read.TString _pos

(* apply a substitution righ to left *)
let apply (s : substitution) (t : Read.typ) : Read.typ =
  List.fold_right (fun (x, u) -> subst u x) s t

(* unify one pair  *)
let rec unify_one (s : Read.typ) (t : Read.typ) : substitution =
  (* a substitution is a list of id * typ
It describes the typ that should be inserted in place of the id *)
  match (s, t) with
  | (Read.TVar (_posl, x), Read.TVar (_posr, y)) ->
     if x = y
     then []
     else [(x, t)]
  | (Read.TUnit _pos
    ,(Read.TUnit __pos
      | Read.TString __pos
     | Read.TU8 __pos)) ->
     []
  | (Read.TU8 _u8pos, (Read.TUnit _pos | Read.TString _pos | Read.TU8 _pos)) ->
     []
  | (Read.TString _posl, (Read.TString _posr | Read.TUnit _posr | Read.TU8 _posr)) ->
     []
  | (Read.TVar (_posl, x), Read.TUnit posr) ->
     [(x, Read.TUnit posr)]
  | (Read.TVar (_posl, x), Read.TString posr) ->
     [x, Read.TString posr]
  | (Read.TVar (_posl, x), Read.TU8 posr) ->
     [x, Read.TU8 posr]
  | (Read.TUnit posl, Read.TVar (_posr, x)) ->
     [(x, Read.TUnit posl)]
  | (Read.TU8 posl, Read.TVar (_posr, x)) ->
     [(x, Read.TU8 posl)]
  | (Read.TString posl, Read.TVar (_posr, x)) ->
     [(x, Read.TString posl)]
  | (Read.TTerm (_posl, _f, _sc)
    ,(Read.TUnit _posr | Read.TString _posr | Read.TU8 _posr)) ->
     failwith "Not unifiable: Head symbol conflict in (Read.TTerm (f, sc), TRead.TUnit (g))"
  | (Read.TVector (_posl, _sc)
    , (Read.TUnit _posr | Read.TString _posr | Read.TArrow (_posr, _, _) | Read.TU8 _posr)) ->
     failwith "Not unifiable: Head symbol conflict in (Read.TVector (f, sc), TRead.TUnit (g))"
  | (Read.TVector (_posl, sc), Read.TVector (_posr, tc)) ->
     unify [(sc, tc)]
  | (Read.TSet (_posl, _sc), (Read.TUnit _posr | Read.TString _posr | Read.TU8 _posr)) ->
     failwith "Not unifiable: Head symbol conflict in (Read.TSet (f, sc), TRead.TUnit (g))"
  | (Read.TTuple (_posl, _sc)
    ,(Read.TUnit _posr | Read.TString _posr | Read.TU8 _posr)) ->
     failwith "Not unifiable: Head symbol conflict in (Read.TTuple (f, sc), Read.TUnit)"
  | (Read.TArrow (_posl, _input, _output)
    ,(Read.TUnit _posr | Read.TString _posr | Read.TU8 _posr)) ->
     failwith "Not unifiable: Head symbol conflict in (Read.TArrow (input, output), TRead.TUnit)"
  | ((Read.TUnit _posl | Read.TU8 _posl | Read.TString _posl)
    , Read.TTerm (_posr, _g, [])) ->
     []
  | ((Read.TUnit _posl | Read.TString _posl | Read.TU8 _posl)
    , Read.TTerm (_posr, _g, _tc)) ->
     failwith "Not unifiable: TRead.TUnit Head symbol conflict in (TRead.TUnit (f), Read.TTerm (g, tc))"
  | ((Read.TUnit _posl | Read.TString _posl | Read.TU8 _posl)
    , (Read.TVector (_posr, _tc) | Read.TSet (_posr, _tc))) ->
     failwith "Not unifiable: TRead.TUnit Head symbol conflict in (TRead.TUnit (f), Read.TVector (g, tc))"
  | ((Read.TUnit _posl | Read.TString _posl | Read.TU8 _posl)
    , Read.TTuple (_posr, [])) ->
     []
  | ((Read.TUnit _posl | Read.TString _posl | Read.TU8 _posl)
    , Read.TTuple (_posr, _tc)) ->
     failwith "Not unifiable: TRead.TUnit Head symbol conflict in ((Read.TUnit | Read.TString | Read.TU8), Read.TTuple tc)"
  | ((Read.TUnit _posl | Read.TString _posl | Read.TU8 _posl)
    , Read.TArrow (_posr, _input, _output)) ->
     failwith "Not unifiable: TRead.TUnit Head symbol conflict in (Read.TUnit, Read.TArrow (input, output))"
  | (Read.TTerm (_posl, _f, _sc)
    ,Read.TArrow (_posr, _input, _output)) ->
     failwith "Not unifiable: Read.TArrow is not Head, symbol conflict"
  | (Read.TTerm (_posl, f, sc)
    , Read.TTerm (_posr, g, tc)) -> (* Read.TTerm * Read.TTerm *)
     if f = g && List.length sc = List.length tc
     then unify (List.combine sc tc)
     else failwith "Not unifiable: Head symbol conflict"
  | ((Read.TVector (_posl, _sc) | Read.TSet (_posl, _sc))
    ,Read.TTerm (_posr, _g, _tc)) ->
     failwith "Not unifiable: Head symbol conflict"
  | (Read.TTerm (_posl, _f, _sc)
    , (Read.TVector (_posr, _tc) | Read.TSet (_posr, _tc))) ->
     failwith "Not unifiable: Head symbol conflict"
  | (Read.TTuple (_posl, _sc)
    , Read.TTerm (_posr, _f, _tc))
    | (Read.TTerm (_posl, _f, _sc), Read.TTuple (_posr, _tc)) ->
     failwith "Not unifiable: Head symbol conflict"
  | (Read.TArrow (_posl, _input, _output)
    ,Read.TTerm (_posr, _g, _tc)) ->
     failwith "Not unifiable: Read.TArrow and Read.TTerm Head symbol conflict"
  | (Read.TVar (_posl, x)
    ,(Read.TTerm (_posr, _, _) as t))
    | ((Read.TTerm (_posl, _,_) as t),
       Read.TVar (_posr, x)) ->
     if occurs x t
     then failwith "not unifiable: ciruclarity in (Read.TVar x, (Read.TTerm (_, _) as t))"
     else [(x, t)]
  | (Read.TSet _, Read.TVector _) | (Read.TVector _, Read.TSet _) | (Read.TTuple _, Read.TVector _) | (Read.TVector _, Read.TTuple _) ->
     failwith "Not unifiable: Head symbol conflict"
  | (Read.TArrow (_posl, _input, _output), Read.TVector (_posr, _tc)) ->
     failwith "Not unifiable: Read.TArrow and Read.TVector Head symbol conflict"
  | (Read.TVar (_posl, x), (Read.TVector (_posr, _) as v))
    | ((Read.TVector (_posl, _) as v), Read.TVar (_posr, x)) ->
     if occurs x v
     then failwith "not unifiable: ciruclarity in (Read.TVar x, (Read.TVector (_, _) as t))"
     else [(x, v)]
  | (Read.TSet (_posl, _sc)
    ,Read.TArrow (_posr, _input, _output)) ->
     failwith "Not unifiable: Read.TArrow is not Head, symbol conflict"
  | (Read.TSet (_posl, sc), Read.TSet (_posr, tc)) ->
     unify [(sc, tc)]
  | (Read.TTuple _, Read.TSet _) | (Read.TSet _, Read.TTuple _) ->
     failwith "Not unifiable: Head symbol conflict"
  | (Read.TArrow (_posl, _input, _output)
    ,Read.TSet (_posr, _tc)) ->
     failwith "Not unifiable: Read.TArrow and Read.TSet Head symbol conflict"
  | (Read.TVar (_pos_var, x)
    ,Read.TSet (pos_set, t))
    | (Read.TSet (pos_set, t)
      , Read.TVar (_pos_var, x)) ->
     if occurs x (Read.TSet (pos_set, t))
     then failwith "not unifiable: ciruclarity in (Read.TVar x, (Read.TSet (_, _) as t))"
     else [(x, (Read.TSet (pos_set, t)))] (* is this correct?  *)
  | (Read.TTuple (_posl, _sc)
    ,Read.TArrow (_posr, _input, _output)) ->
     failwith "Not unifiable: Read.TArrow is not Head, symbol conflict"
  | (Read.TTuple (_posl, sc), Read.TTuple (_posr, tc)) ->
     if List.length sc = List.length tc
     then unify (List.combine sc tc)
     else failwith "Not unifiable: Head symbol conflict"
  | (Read.TArrow (_posl, _input, _output), Read.TTuple (_posr, _tc)) ->
     failwith "Not unifiable: Read.TArrow and Read.TTuple Head symbol conflict"
  | (Read.TVar (_pos_var, x)
    ,(Read.TTuple (_pos_tup, _) as t))
    | ((Read.TTuple (_pos_tup, _) as t)
      ,Read.TVar (_pos_var, x)) ->
     if occurs x t
     then failwith "not unifiable: ciruclarity in (Read.TVar x, (Read.TTuple (_, _) as t))"
     else [(x, t)]
  | (Read.TArrow (_posl, f_input, f_output), Read.TArrow (_posr, g_input, g_output)) ->
     unify (List.combine
              [f_input; f_output]
              [g_input; g_output])
  | (Read.TVar (_pos_var, x), (Read.TArrow (_pos_arr, _, _) as t))
    | ((Read.TArrow (_pos_arr, _,_) as t), Read.TVar (_pos_var, x)) ->
     if occurs x t
     then failwith "not unifiable: ciruclarity in (Read.TVar x, (Read.TArrow (_, _) as t))"
     else [(x, t)]
  | (_, Read.TDict _) -> failwith "COOL TDICT on the right"
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
  Read.TTerm (negpos, k, v)

let v s =
  Read.TVar (negpos, s)

let unify_tests =
  [("Unify: Infer"
   , apply (unify [v 1, (Read.TTuple (negpos, [(v 5); (v 4)]))
                  ;v 5, Read.TVector (negpos, (v 7))
		  ;v 4, Read.TSet (negpos, Read.TU8 negpos)
		  ;v 6, Read.TU8 negpos
		  ;v 7, Read.TU8 negpos
		  ;v 6, v 3
		  ;v 7, v 3
		  ;v 2, Read.TArrow (negpos, v 1, v 3)])
       (v 2)
     = Read.TArrow
         (negpos,
          Read.TTuple (negpos
                      ,[Read.TVector (negpos, Read.TU8 negpos)
                       ;Read.TSet (negpos, Read.TU8 negpos)])
          ,Read.TU8 negpos))
  ;("Unify: Infer unit"
   , apply (unify [v 1, v 2
                  ;v 2, Read.TUnit negpos])
       (v 1)
     = Read.TUnit negpos)]

let string_of_typ = Util.comp Read.string_of_char_list Read.string_of_typ

let string_of_equation = function
  | (ty1, ty2) ->
     string_of_typ ty1
     ^ " = "
     ^ string_of_typ ty2

type env_key =
  | EInt of int
  | EStr of string
type env = (env_key * Read.typ) list

let empty_env = []

let string_of_env env =
  env
  |> List.map (fun (str,ty) -> str ^ ": " ^ string_of_typ ty)
  |> String.concat ", "

exception InferError of string

(* infer all facts (equations) as possible about an expr *)
let infer (expr: Read.expr): ((equation list * Read.typ), string) result =
  let rec infer_rec
            (equations: equation list)
            (goals: (env * Read.expr * Read.typ) list)
          : equation list =
    match goals with
    | [] -> equations
    | (env, expr, ty) :: rest_of_goals ->
       (match expr with
        | Read.Sym (pos_sym, x) ->
           (match List.assoc_opt (EStr x) env with
            | Some x_from_env ->
               let new_equations = (x_from_env, ty) :: equations in
               infer_rec new_equations rest_of_goals
            | None when x = "Log" ->
               let new_equations = (ty, ty) :: equations in (* Log is just Log *)
               infer_rec new_equations rest_of_goals
            | None -> failwith (Util.str ["Can't infer type of the Sym '"
                                         ;Read.string_of_char_list
                                            (Read.string_of_expr expr)
                                         ;"'. pos: "
                                         ;Read.string_of_position pos_sym]))
        | Read.App (pos, f, argument) ->
           let input_type = gensym () in
           let new_goals =
             (env, f, Read.TArrow(pos, input_type, ty))
             :: (env, argument, input_type)
             :: rest_of_goals in
           infer_rec equations new_goals
        | Read.Lam (pos_lam, (PSym (_pos_sym, x), body) :: _rest) ->
           let input_type = gensym () in
           let output_type = gensym () in
           let new_env = ((EStr x), input_type) :: env in
           let new_goals = (new_env, body, output_type) :: rest_of_goals in
           let new_equations = (ty
                               ,Read.TArrow(pos_lam
                                            ,input_type
                                            ,output_type)) :: equations in
           infer_rec new_equations new_goals
        | Read.Lam (_pos_lam, (Read.PTag (_pos_ptag, _name, _child), _body) :: _rest) ->
           raise (InferError "lam with ptag not supported")
        | Read.Lam (pos, []) -> failwith (Util.str ["A lambda binding nothing makes no sense...pos: "
                                                    ;Read.string_of_position pos])
        | Read.Unit pos ->
           let new_equations = (ty, Read.TUnit pos) :: equations in
           infer_rec new_equations rest_of_goals
        | Read.U8 (pos, _n) ->
           infer_rec ((ty, Read.TU8 pos) :: equations) rest_of_goals
        | Read.String (pos, _s) ->
           let new_equations = (ty, Read.TString pos) :: equations in
           infer_rec new_equations rest_of_goals
        | Read.Tuple (pos, children) ->
           (* For each child, create a new TSym *)
           (* For each `(child, child_tsym)`, create a goal
              that says (env, child, child_tsym)
              Also create a new equation saying `(ty, Read.TTuple (pos, child_tsyms))`
*)
           let childrens_tsyms: Read.typ list =
             List.map (fun _ -> gensym ()) children in
           (* Current type `ty` is a <childrens_tsyms> i.e. a tuple *)
           let new_equations =
             (ty, Read.TTuple (pos, childrens_tsyms)) :: equations in
           let child_goal child child_tsym =
             env,
             child,
             child_tsym in
           let new_goals = List.concat
                             [(List.map
                                 (fun (c, t) -> child_goal c t)
                                 (List.combine children childrens_tsyms))
                             ;rest_of_goals] in
           infer_rec new_equations new_goals
        | Read.Vector (_pos, _children) ->
           raise (InferError "Read.Vector not implemented")
        | Read.Dict (_pos, _keys_and_vals) ->
           raise (InferError "Read.Dict not implemented")
        | Read.Set (_pos, _children) ->
           raise (InferError "Read.Set not implemented")
        | Read.Ann (_pos, _given_typ, _expr) ->
           raise (InferError "Read.Ann not implemented")
       (* | Read.TaggedExpr (pos_tag
        *                    ,tag_name
        *                    ,tagged_value) ->
        *    let this_typ = Read.TVar (pos_tag, 1337) in
        *    let tagged_value_typ = Read.TVar (pos_tag, 1338) in
        *    let new_equations = (ty
        *                        ,this_typ)
        *                        :: equations in
        *    let new_goals = (env, tagged_value, tagged_value_typ) :: rest_of_goals in
        *    infer_rec new_equations new_goals
        * | Read.Match (pos_match
        *               ,tag
        *               ,((PSym (pos_psym
        *                       ,pattern)
        *                 ,body)
        *                 :: rest_of_cases)) ->
        *    let body_ty = gensym () in
        *    let new_equations = (ty, body_ty) :: equations in
        *    let new_goals = (env, body, body_ty)
        *                    :: (env, Read.Match (pos_match
        *                                         ,tag
        *                                         ,rest_of_cases)
        *                        ,ty)
        *                    :: rest_of_goals in
        *    infer_rec new_equations new_goals
        * | Read.Match (pos_match
        *               ,tag      (\* should be named something like "question" *\)
        *               ,((Read.PTag (pos_ptag
        *                             ,name
        *                             ,child)
        *                 ,body)
        *                 :: rest_of_cases)) ->
        *    (\* FIXME HERE *\)
        *    failwith "Read.Match of PTag not implemented"
        * (\* DONE *\)
        * | Read.Match (match_pos, tag, []) ->
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
      infer (Read.App (negpos
                       ,Read.Lam (negpos, [PSym (negpos, "x"), Sym (negpos, "x")])
                       ,Read.Lam (negpos, [PSym (negpos, "y"), Sym (negpos, "y")]))))
     = Ok ([(Read.TVar (negpos, 4), Read.TVar (negpos, 5));
            (Read.TVar (negpos, 1), Read.TArrow (negpos
                                               ,Read.TVar (negpos, 4)
                                               ,Read.TVar (negpos, 5)));
         (Read.TVar (negpos, 2), Read.TVar (negpos, 3));
         (Read.TArrow (negpos, Read.TVar (negpos, 1), Read.TVar (negpos, 0)),
          Read.TArrow (negpos, Read.TVar (negpos, 2), Read.TVar (negpos, 3)))],
        Read.TVar (negpos, 0)))
  ;("Type of k"
   , (__gensym_state__ := -1;
      infer_and_unify (Read.Lam (negpos, [PSym (negpos, "x")
                                          ,Read.Lam (negpos
                                                     ,[PSym (negpos, "y")
                                                      ,Sym (negpos, "x")])])))
     = Ok (Read.TArrow (negpos
                        ,Read.TVar (negpos, 4)
                        ,Read.TArrow (negpos
                                  ,Read.TVar (negpos, 3)
                                  ,Read.TVar (negpos, 4)))))
  ; ("Type of <1 1>",
     (__gensym_state__ := -1;
      infer_and_unify (Read.Tuple (negpos
                                   ,[(Read.U8 (negpos, 1))
                                    ;(Read.U8 (negpos, 1))]))
      = Ok (Read.TTuple (negpos, [(TU8 negpos); (TU8 negpos)]))) )
  ; ("Type of <<1 1> <1 1>>",
     (__gensym_state__ := -1;
      infer_and_unify (Read.Tuple (negpos
                                   ,[(Read.Tuple (negpos
                                                 ,[(Read.U8 (negpos, 1))
                                                  ;(Read.U8 (negpos, 1))]))
                                    ;(Read.Tuple (negpos
                                                 ,[(Read.U8 (negpos, 1))
                                                  ;(Read.U8 (negpos, 1))]))]))
      = Ok (Read.TTuple (negpos,
                         [Read.TTuple (negpos,
                                       [(TU8 negpos);
                                        (TU8 negpos)]);
                          Read.TTuple (negpos,
                                       [(TU8 negpos);
                                        (TU8 negpos)])]))) )
  ; ("Type of Dict"
    ,(__gensym_state__ := -1;
      infer_and_unify (Read.Dict (negpos
                                  ,[Read.U8 (negpos, 1)
                                   ,Read.Lam (negpos, [PSym (negpos, "x"), Sym (negpos, "x")])]))
      = Ok (Read.TDict (negpos
                        ,TU8 negpos
                        ,TArrow (negpos
                            ,TU8 negpos
                            ,TU8 negpos)))))
   (* ;("match a union"
    *  , (__gensym_state__ := -1;
    *     infer_and_unify (Read.Match ((0, 83)
    *                                  ,TaggedExpr ((8, 12)
    *                                              ,"Some"
    *                                              ,U8 ((17, 21), 1337))
    *                                  ,[(PTag ((43, 47), "Some", Sym ((48, 49), "n"))
    *                                    ,Sym ((51, 52), "n"));
    *
    *                                    (PSym ((71, 75), "None")
    *                                    ,U8 ((80, 81), 0))]))
    *     = Read.TU8 negpos)) *)
   (* ;("infer (Some value)"
    *  , (__gensym_state__ := -1;
    *     (\* let option = Read.TUnion (negpos
    *      *                           ,"a"
    *      *                           ,["Some", Read.TVar (negpos, 123456)
    *      *                            ;"None", Read.TUnit negpos]) in *\)
    *     infer_and_unify (Read.TaggedExpr (negpos
    *                                       ,"Some"
    *                                       ,Read.U8 (negpos, 1337)))
    *     = Read.TVar ((-1, -1), 1337)
    *  (\* = Read.TUnion (negpos
    *   *                ,"a"
    *      *                ,[("Some", Read.TU8 negpos)
    *      *                 ;("None", Read.TUnit negpos)]) *\)))
    * ;("infer None"
    *  , (__gensym_state__ := -1;
    *     (\* let option = Read.TUnion (negpos,
    *      *                            "a"
    *      *                            ,["Some", Read.TVar (negpos, 123456)
    *      *                             ;"None", Read.TUnit negpos]) in *\)
    *     infer_and_unify (Read.TaggedExpr (negpos
    *                                       ,"None", Read.U8 (negpos, 1337)))
    *     = Read.TVar ((-1, -1), 1337) (\* = option *\))) *)]
