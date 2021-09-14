let rec pow a = function
  | 0 -> 1
  | 1 -> a
  | n -> let b = pow a (n / 2) in
         b * b * (if n mod 2 = 0 then 1 else a)

let arrow = Type.Function.create
let ty_var global_env = Type.Type.TyVar (Type.TypeVariable.create global_env)
let rec zip xl yl =
  match (xl, yl) with
  | (x::xs, y::ys) -> (x, y) :: zip xs ys
  | ([], []) -> []
  | _ -> assert false

let my_U8 = Type.Type.TyOp (Type.TypeOperator.create "U8" [])
(* let my_Bool = Type.Type.TyOp (Type.TypeOperator.create "Bool" []) *)
let my_String = Type.Type.TyOp (Type.TypeOperator.create "String" [])
let my_Unit = Type.Type.TyOp (Type.TypeOperator.create "<>" [])
let my_Tuple members = Type.Type.TyOp (Type.TypeOperator.create "Tuple" members)
let my_Vector child = Type.Type.TyOp (Type.TypeOperator.create "Vector" [child])
let my_Set members = Type.Type.TyOp (Type.TypeOperator.create "Set" [members])
let my_Dict key value = Type.Type.TyOp (Type.TypeOperator.create "Dict" [key; value])

module TVSet = Set.Make(Type.TypeVariable)

exception ParseError of string
exception TypeError of string
exception UnificationError of string
type analyze_error
  = ParseError of string
  | TypeError of string
  | UnificationError of string

let rec analyse gensym_state node (env: (string * Type.Type.t) list) non_generic: Type.Type.t =
  match node with
  | Expr.Sym (_pos, name) -> get_type gensym_state name env non_generic
  | Expr.App (_pos, fn, arg) ->
     let fun_type = analyse gensym_state fn env non_generic in
     let arg_type = analyse gensym_state arg env non_generic in
     let result_type_param = Type.Type.TyVar (Type.TypeVariable.create gensym_state) in
     unify gensym_state (Type.Function.create arg_type result_type_param) fun_type;
     result_type_param
  | Expr.Lam (_pos, []) ->
      failwith "Can't type infer lambda without args"
  | Expr.Lam (_pos, (PSym (_psym_pos, v), body) :: _rest) ->
     let arg_type = Type.TypeVariable.create gensym_state in
     let arg_type_param = Type.Type.TyVar arg_type in
     (* let new_env = StringMap.add v arg_type_param env in *)
     let new_env = (v, arg_type_param) :: env in
     let new_non_generic = TVSet.add arg_type non_generic in
     let result_type = analyse gensym_state body new_env new_non_generic in
     Type.Function.create arg_type_param result_type
  | Expr.Lam (_, (PTag (_, _, _), _)::_) ->
    failwith "TODO can't yet type check functions of patterns"
  | Expr.Let (_pos, v, defn, body) ->
     let defn_type = analyse gensym_state defn env non_generic in
     (* let new_env = StringMap.add v defn_type env in *)
     let new_env = (v, defn_type) :: env in
     analyse gensym_state body new_env non_generic
  | Expr.Letrec (_pos, v, defn, body) ->
     let new_type = Type.TypeVariable.create gensym_state in
     let new_type_param = Type.Type.TyVar new_type in
     (* let new_env = StringMap.add v new_type_param env in *)
     let new_env = (v, new_type_param) :: env in
     let new_non_generic = TVSet.add new_type non_generic in
     let defn_type = analyse gensym_state defn new_env new_non_generic in
     unify gensym_state new_type_param defn_type;
     analyse gensym_state body new_env non_generic
  | Expr.Unit _pos -> assert false
  | Expr.U8 (_n, _pos) ->
    my_U8
  | Expr.Ann (_pos, expected_typ, given_expr) ->
    let given_expr_type = analyse gensym_state given_expr env non_generic in
    unify gensym_state expected_typ given_expr_type;
    given_expr_type
  | Expr.String (_pos, _s) -> my_String
  (* | Expr.None _pos -> my_Unit *)
  | Expr.Vector (_pos, xs) ->
    let new_type = Type.TypeVariable.create gensym_state in
    let new_type_param = Type.Type.TyVar new_type in
    let xs_types = (List.map (fun expr -> analyse gensym_state expr env non_generic) xs) in
    List.iter (fun ty ->
        unify gensym_state new_type_param ty;)
      (xs_types);
    my_Vector new_type_param
  | Expr.Dict (_pos, key_value_pairs) ->
    let keys = List.map fst key_value_pairs in
    let values = List.map snd key_value_pairs in
    let unify_many (xs: Expr.expr list): Type.Type.t =
      let new_type = Type.TypeVariable.create gensym_state in
      let new_type_param = Type.Type.TyVar new_type in
      let xs_types = (List.map (fun expr -> analyse gensym_state expr env non_generic) xs) in
      List.iter (fun ty ->
        unify gensym_state new_type_param ty;)
        (xs_types);
      new_type_param
    in
    my_Dict (unify_many keys) (unify_many values)
  | Match (_pos, _x, []) ->
    failwith "Match with no cases makes no sense"
  | Match (_pos, x, cases) ->
    let new_type = Type.TypeVariable.create gensym_state in
    let new_type_param = Type.Type.TyVar new_type in
    (* (match x
              y y
              z z)
     * Return type is type of `((λ y y) x)` and `((λ z z) x)` given they are equal *)
    let appize x case = Expr.App ((-1, -1),
                                  Expr.Lam ((-1,-1),
                                            [case]),
                                  x) in
    let cases_appized_types = cases
                              |> List.map (appize x)
                              |> List.map
                                   (fun expr ->
                                     analyse gensym_state expr env non_generic) in
    List.iter
      (fun ty ->
        unify gensym_state new_type_param ty;)
      cases_appized_types;
    new_type_param
  | (Tuple (_, _)|Set (_, _)) ->
    failwith "TODO `analyze` not yet implemented"
and string_of_context env =
  let rec inner acc = function
    | (name, typ) :: rest ->
       inner ("(" ^ name ^ " " ^ (Type.Type.to_string env typ) ^ ")") rest
    | [] -> acc ^ ")"
  in inner "("

and context_contains_constructor context name =
  let rec search = function
    | (_ctor_name, Type.Type.TyTagUnion ctors) :: rest ->
       if List.mem_assoc name ctors
       then true
       else search rest
    | (_, _) :: rest -> search rest
    | [] -> false
  in search context

and find_enum_matching_ctor context name =
  let rec search = function
    | (_ctor_name, Type.Type.TyTagUnion ctors) :: rest ->
       if List.mem_assoc name ctors
       then List.assoc_opt name ctors
       else search rest
    | (_, _) :: rest -> search rest
    | [] -> None
  in search context

and get_type global_env name context non_generic =
  if List.mem_assoc name context
  then fresh
         global_env
         (* (StringMap.find name context) *)
         (List.assoc name context)
         non_generic
  else if is_integer_literal name
  then my_U8
  else if context_contains_constructor context name
  then match (find_enum_matching_ctor context name) with
       | Some enum_type ->
          enum_type
       | None -> raise (ParseError
                          (Printf.sprintf
                             "TypeError: Can't find enum for tag %s"
                             name))
  else raise (ParseError ("Undefined symbol in type inferrer: " ^ name))

and fresh global_env t non_generic: Type.Type.t =
  let mappings = Hashtbl.create 30 in
  let rec freshrec tp: Type.Type.t =
    let p = prune tp in
    match p with
    | Type.Type.TyVar tv ->
       let non_generic_list =
         List.map (fun a -> Type.Type.TyVar a) (TVSet.elements non_generic) in
       if is_generic tv non_generic_list
       then begin
           if not (Hashtbl.mem mappings p)
           then Hashtbl.replace mappings p (Type.Type.TyVar (Type.TypeVariable.create global_env));
           Hashtbl.find mappings p
         end
       else p
    | Type.Type.TyTag (name, child_type) ->
       Type.Type.TyTag (name, freshrec child_type)
    | Type.Type.TyTagUnion child_types ->
       Type.Type.TyTagUnion (List.map
                          (fun (name, x) -> (name, freshrec x))
                          child_types)
    | Type.Type.TyOp (name, child_types) ->
       Type.Type.TyOp (Type.TypeOperator.create
                    name
                    (List.map (fun x -> freshrec x) child_types))
  in freshrec t

(* Har igång type inferrence som kan göra letrec nu, Hindley Milner.
 *
 * Tänker på unification - man har ju två varianter av expr, Term och Symbol, där Term har ett namn och en lista med expressions.
 *
 * Med det kan man implementera OCH-relationer, alltså att "->" har två variablar "a" och "b". Den är alltså "forall", och implementerar "och"-relationen.
 *
 * "Eller" eller "or"-relationen är ännu inte implementerad, som i hur en (Maybe a) är en (Just a) eller None. Tänker att man behöver en ny variant på expr förutom "Term", som istället kunde heta "OrTerm" eller så. En `| OrTerm of string * expr list`. Så när unify finner ut typen av en variabel, och den variabeln i evaluation context pekar på en OrTerm, *)

(* Unify the two types t1 and t2
Makes the types t1 and t2 the same *)
and unify gensym_state t1 t2: unit =
  let a = prune t1 in
  let b = prune t2 in
  match (a, b) with
  | (Type.Type.TyVar tyvar, _) ->
     if a <> b
     then begin
         if occurs_in_type tyvar b
         then raise (TypeError "recursive unification")
         else tyvar.Type.TypeVariable.instance <- Some b
       end
  | (_ (* Type.Type.TyOp(_top) *)
    , Type.Type.TyVar _tyvar) ->
     unify gensym_state b a
  (* | (Type.Type.TyOp (top1_name, top1_types), Type.Type.TyTag (tytag_name, tytag_type)) -> *)
  (*
(let Maybe (enum (Maybe a) (Just a) None)
  (Maybe Just (u8 1)))
TyEnum ("Maybe", ty_var "a", [Ty])
 *)
  | (Type.Type.TyOp (top1_name, top1_types), Type.Type.TyOp (top2_name, top2_types)) ->
     (* Same names and arity *)
     let top1_types_size = (List.length top1_types) in
     let top2_types_size = (List.length top2_types) in
     (* JESPER! Här kollar vi att båda Terms eller Type Operators (TyOp) har samma namn och antal argument *)
     (* Med OR type operators aka terms, så måste vi istället kolla om den ena eller andra TypeOperator har label som en "child" av den andra. Detta för att "(Just a)" inte är = (Maybe a), men matchar child of (Maybe a).  *)
     if ((top1_name <> top2_name) || (top1_types_size <> top2_types_size))
     then raise (TypeError ("Type mismatch "
                            ^ (Type.TypeOperator.to_string
                                 gensym_state
                                 (top1_name, top1_types))
                            ^ " != "
                            ^ (Type.TypeOperator.to_string
                                 gensym_state
                                 (top2_name, top2_types))));
     (* Här kollar den bara om TypeOperators top1 och top2 är lika - men med OR behöver den också kolla om den ena är "child" till den andra, vilket är enkelt som att kolla om List.contains i den ena eller andras children. Kom ihåg, en typ = Sym of string | TypeOperator of string * typ list | TypeOperatorOr of string * typ list.

Så (Maybe a) => (TypeOperatorOr "Maybe" [Sym "a"])
Och (Just a) => (TypeOperator "Just" [Sym "a"])
unify (Maybe a) (Just b) => (Maybe a)*)
     List.iter2 (unify gensym_state) (top1_types) (top2_types)
(* | _ -> raise (UnificationError "Not unified") *)
  | (Type.Type.TyTagUnion (cases), Type.Type.TyTag (tag_name, tag_typ))|
    (Type.Type.TyTag (tag_name, tag_typ), Type.Type.TyTagUnion (cases))->
     (match List.assoc_opt tag_name cases with
      | Some canonical_typ ->
         (* canonical type is what we expect - it should unify with tag_type *)
         unify gensym_state canonical_typ tag_typ
      | None -> raise (TypeError ("Union Tag mismatch "
                                  ^ Type.Type.to_string gensym_state (Type.Type.TyTagUnion (cases))
                                  ^ "not matching "
                                  ^ Type.Type.to_string gensym_state tag_typ)))
  | (Type.Type.TyOp (_, _), (Type.Type.TyTag _|TyTagUnion _))|
      ((TyTag _|TyTagUnion _), TyOp (_, _)) ->
     raise (TypeError ("TyOp and TyTag|TyTagUnion don't unify"))
  | (Type.Type.TyTag (t1_name, t1_typ), Type.Type.TyTag (t2_name, t2_typ)) ->
     if t1_name = t2_name
     then unify gensym_state t1_typ t2_typ
     else raise (TypeError "Given two TyTag but they are not of the same tag name")
  | (TyTagUnion _, (TyTagUnion _)) ->
     unify gensym_state a b

and prune (t: Type.Type.t) =
  match t with
  | Type.Type.TyVar tv ->
     (match tv.Type.TypeVariable.instance with
      | Some stv ->
         tv.Type.TypeVariable.instance <- Some (prune stv);
         stv
      | None -> t)
  | _ -> t

and is_generic (v: Type.TypeVariable.t) non_generic = not (occurs_in v non_generic)

and occurs_in_type (v: Type.TypeVariable.t) t2 =
  let pruned_t2 = prune t2 in
  match pruned_t2 with
  | Type.Type.TyVar tv when tv = v -> true
  | Type.Type.TyOp  (_name, tyop_types) -> occurs_in v tyop_types
  | _ -> false

and occurs_in (t: Type.TypeVariable.t) types = List.exists (fun t2 -> occurs_in_type t t2) types

and is_integer_literal name =
  try ignore (int_of_string name);
      true
  with Failure _ -> false

let try_exp global_env env node =
  Printf.printf "%s: " (Expr.string_of_expr global_env node);
  try print_endline (Type.Type.to_string
                       global_env
                       (analyse
                          global_env
                          node
                          env
                          TVSet.empty))
  with
  | ParseError e | TypeError e ->
     print_endline e

let analyze_result global_env env node =
  try Ok (analyse global_env node env TVSet.empty)
  with
  | ParseError e -> Error (ParseError e)
  | TypeError e -> Error (TypeError e)

let type_infer_tests =
  [( let actually =
       (let global_env = Type.new_gensym_state () in
        (analyse
           global_env
           (Expr.Lam ((-1, -1),
                      [((Expr.PSym ((-1, -1), "x"))
                      , (Expr.Lam
                           ((-1, -1),
                            [(Expr.PSym ((-1, -1), "y")
                           , Expr.Sym ((-1, -1), "x"))])))]))
           []
           TVSet.empty)) in
     Printf.sprintf
       "type of K combinator is (-> a b a), actually: %s"
       (Type.Type.to_string
          (Type.new_gensym_state ())
          actually)
   , actually
     = (Type.Type.TyOp
          ("->",
           [Type.Type.TyVar {Type.TypeVariable.id = 0; name = ""; instance = None};
            Type.Type.TyOp
              ("->",
               [Type.Type.TyVar {Type.TypeVariable.id = 1; name = ""; instance = None};
                Type.Type.TyVar {Type.TypeVariable.id = 0; name = ""; instance = None}])])))]

    (* let () =
 *   let var1 = Type.Type.TyVar (Type.TypeVariable.create ()) in
 *   let var2 = Type.Type.TyVar (Type.TypeVariable.create ()) in
 *   let pair_type = Type.Type.TyOp (Type.TypeOperator.create "*" [var1; var2]) in
 *   let var3 = Type.Type.TyVar (Type.TypeVariable.create ()) in
 *   let my_env =
 *     StringMap.empty
 *     |> StringMap.add "pair" (Type.Function.create var1 (Type.Function.create var2 pair_type))
 *     |> StringMap.add "true" my_bool
 *     |> StringMap.add "cond"
 *          (Type.Function.create my_bool
 *             (Type.Function.create var3
 *                (Type.Function.create var3 var3)))
 *     |> StringMap.add "zero" (Type.Function.create my_int my_bool)
 *     |> StringMap.add "pred" (Type.Function.create my_int my_int)
 *     |> StringMap.add "times" (Type.Function.create my_int (Type.Function.create my_int my_int))
 *   in let pair =
 *        (Expr.Apply
 *           ((Expr.Apply
 *               ((Expr.Sym "pair"),
 *                (Expr.Apply
 *                   ((Expr.Sym "f"), (Expr.Sym "4")))),
 *             (Expr.Apply
 *                ((Expr.Sym "f"),
 *                 (Expr.Sym "true"))))))
 *      in let examples =
 *           [
 *             (\* factorial *\)
 *             (Expr.Letrec              (\* letrec factorial = *\)
 *                ("factorial",
 *                 Expr.Lam           (\* fun n -> *\)
 *                   ("n",
 *                    Expr.Apply (
 *                        Expr.Apply (     (\* cond (zero n) 1 *\)
 *                            Expr.Apply     (\* cond (zero n) *\)
 *                              (Expr.Sym "cond",
 *                               Expr.Apply (Expr.Sym "zero", Expr.Sym "n")),
 *                            Expr.Sym "1"),
 *                        Expr.Apply (     (\* times n *\)
 *                            Expr.Apply (Expr.Sym "times", Expr.Sym "n"),
 *                            Expr.Apply (
 *                                Expr.Sym "factorial",
 *                                Expr.Apply (Expr.Sym "pred", Expr.Sym "n")
 *                   )))),          (\* in *\)
 *                 Expr.Apply (Expr.Sym "factorial", Expr.Sym "5")));
 *
 *             (\* Should fail
 *              * fun x -> (pair (x 3) (x true))
 *              *\)
 *             Expr.Lam("x",
 *                         Expr.Apply(
 *                             Expr.Apply(Expr.Sym "pair",
 *                                        Expr.Apply(Expr.Sym "x", Expr.Sym "3")),
 *                             Expr.Apply(Expr.Sym "x", Expr.Sym "true")));
 *
 *             (\* (pair (f 3)) (f true) *\)
 *             Expr.Apply(
 *                 Expr.Apply(Expr.Sym "pair", Expr.Apply(Expr.Sym "f", Expr.Sym "4")),
 *                 Expr.Apply(Expr.Sym "f", Expr.Sym "true"));
 *
 *             (\* let f = (fn x -> x) in ((pair (f 4)) (f true)) *\)
 *             Expr.Let("f", Expr.Lam("x", Expr.Sym "x"), pair);
 *
 *             (\* fun f -> f f *\)
 *             (\* This should fail (recursive type definition) *\)
 *             Expr.Lam("f", Expr.Apply(Expr.Sym "f", Expr.Sym "f"));
 *
 *             (\* let g = fun f -> 5 in g g *\)
 *             Expr.Let("g", Expr.Lam("f", Expr.Sym "5"),
 *                      Expr.Apply(Expr.Sym "g", Expr.Sym "g"));
 *
 *             (\* example that demonstrates generic and non-generic variables *\)
 *             (\* fun g -> let f = fun x -> g in pair (f 3, f true) *\)
 *             Expr.Lam("g",
 *                         Expr.Let("f",
 *                                  Expr.Lam("x", Expr.Sym "g"),
 *                                  Expr.Apply(
 *                                      Expr.Apply(
 *                                          Expr.Sym "pair",
 *                                          Expr.Apply(Expr.Sym "f", Expr.Sym "3")),
 *                                      Expr.Apply(Expr.Sym "f", Expr.Sym "true"))));
 *
 *             (\* function composition *\)
 *             (\* fun f -> fun g -> fun arg -> f g arg *\)
 *             Expr.Lam("f",
 *                         Expr.Lam("g",
 *                                     Expr.Lam("arg",
 *                                                 Expr.Apply(
 *                                                     Expr.Sym "g",
 *                                                     Expr.Apply(
 *                                                         Expr.Sym "f",
 *                                                         Expr.Sym "arg")))))
 *
 *
 *           ]
 *         in
 *         List.iter (fun ex -> try_exp my_env ex) examples *)
