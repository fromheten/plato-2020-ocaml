let rec pow a = function
  | 0 -> 1
  | 1 -> a
  | n -> let b = pow a (n / 2) in
         b * b * (if n mod 2 = 0 then 1 else a)

type env =
  { mutable next_variable_id : int
  ; mutable next_variable_name : char }

let new_env () = {next_variable_id = 0
                 ;next_variable_name = 'a'}

(* let global_env_old = new_env () *)

module rec TypeVariable : sig
         type t = { id: int
                  ; mutable name: string
                  ; mutable instance: Type.t option }
         val create: env -> t
         val name: env -> t -> string
         val to_string: env -> t -> string
         val compare: t -> t -> int
         val hash: t -> int
         val equal: t -> t -> bool
       end = struct
  type t = {id: int
           ;mutable name: string
           ;mutable instance: Type.t option }
  let create global_env =
    global_env.next_variable_id <- global_env.next_variable_id + 1;
    { id = global_env.next_variable_id - 1
    ; name = ""
    ; instance = None }
  let name global_env tv =
    if tv.name = ""
    then begin
        tv.name <- Char.escaped global_env.next_variable_name;
        global_env.next_variable_name <- Char.chr ((Char.code global_env.next_variable_name) + 1)
      end;
    tv.name

  let to_string global_env tv =
    match tv.instance with
    | None -> name global_env tv
    | Some typ ->
      Type.to_string global_env typ

  let compare t1 t2 = t2.id - t1.id
  let hash tv = tv.id
  let equal tv1 tv2 = tv1.id = tv2.id
end

   and TypeOperator: sig
     (* type t = { name: string; types: Type.t list} *)
     type t = string * Type.t list
     val create: string -> Type.t list -> t
     val to_string: env -> t -> string
   end = struct
     type t = string * Type.t list
     let create n tl = (n, tl)
     let to_string global_env = function
         (name, types) ->
         (match types with
          | [] -> name
          | hd::tl::[] ->
             Printf.sprintf "(%s %s %s)"
               name
               (Type.to_string global_env hd)
               (Type.to_string global_env tl)
          | _ -> types
                 |> List.map (Type.to_string global_env)
                 |> List.fold_left (fun a b -> a ^ " " ^ b) ""
                 |> Printf.sprintf "%s %s" name)
   end

   and Type: sig
     type t = TyVar of TypeVariable.t
            | TyTag of (string * t)
            | TyTagUnion of (string * t) list
            | TyOp of TypeOperator.t
     val to_string: env -> t -> string
   end = struct
     type t = TyVar of TypeVariable.t
            | TyTag of (string * t)
            | TyTagUnion of (string * t) list
            | TyOp of TypeOperator.t
     let rec to_string global_env = function
       | TyVar tv -> TypeVariable.to_string global_env tv ^ "-" ^ string_of_int tv.id ^ tv.name
       | TyTag (tag, tagged_typ) ->
          "(" ^ tag ^ " " ^ to_string global_env tagged_typ ^ ")"
       | TyTagUnion cases ->
          "(union " ^ String.concat " " (List.map
                                           (to_string global_env)
                                           (List.map (fun x -> TyTag x) cases))
       | TyOp top -> TypeOperator.to_string global_env top
   end

   and Function: sig
     val create: Type.t -> Type.t -> Type.t
   end = struct
     let create from_type to_type =
       Type.TyOp ("->", [from_type; to_type])
   end
let arrow = Function.create
let ty_var global_env = Type.TyVar (TypeVariable.create global_env)
let rec zip xl yl =
  match (xl, yl) with
  | (x::xs, y::ys) -> (x, y) :: zip xs ys
  | ([], []) -> []
  | _ -> assert false

let my_U8 = Type.TyOp (TypeOperator.create "U8" [])
(* let my_Bool = Type.TyOp (TypeOperator.create "Bool" []) *)
let my_String = Type.TyOp (TypeOperator.create "String" [])
let my_Unit = Type.TyOp (TypeOperator.create "<>" [])
let my_Tuple members = Type.TyOp (TypeOperator.create "Tuple" members)
let my_Vector child = Type.TyOp (TypeOperator.create "Vector" [child])
let my_Set members = Type.TyOp (TypeOperator.create "Set" [members])
let my_Dict key value = Type.TyOp (TypeOperator.create "Dict" [key; value])

module TVSet = Set.Make(TypeVariable)
(* module StringMap = Map.Make(String) *)

module Expr = struct
  type t =
    | Ident of string
    | Apply of t * t
    | Lambda of string * t
    | Let of string * t * t
    | Letrec of string * t * t
    | None
    | U8 of int
    | Unit
    | String of string
    | Annotation of Type.t * t
    | Vector of t list
    | Dict of (t * t) list

  let rec to_string gensym_env e =
    let to_string = to_string gensym_env in
    match e with
    | Ident s -> s
    | Apply (fn, arg) ->
       Printf.sprintf "(%s %s)" (to_string fn) (to_string arg)
    | Lambda (v, body) ->
       Printf.sprintf "(fun %s -> %s)" v (to_string body)
    | Let (v, defn, body) ->
       Printf.sprintf "(let %s = %s in %s)" v (to_string defn) (to_string body)
    | Letrec (v, defn, body) ->
       Printf.sprintf "(let rec %s = %s in %s)" v (to_string defn) (to_string body)
    | None -> "None"
    | U8 n -> string_of_int n
    | String s -> "\"" ^ s ^ "\""
    | Annotation (t, expr) -> Printf.sprintf "(Ann %s %s)"
                                (Type.to_string gensym_env t)
                                (to_string expr)
    | Unit -> "<>"
    | Vector xs ->
      Printf.sprintf "[%s]" (Util.str
                               (List.map
                                  (Util.comp (fun x -> (Printf.sprintf "%s " x))
                                     to_string)
                                  xs))
    | Dict kvs ->
      Printf.sprintf "{%s}" (Util.str
                               (List.map
                                  (Util.comp (fun (k, v) -> (Printf.sprintf "%s %s" k v))
                                     (fun (k, v) -> (to_string k, to_string v)))
                                  kvs))
end

exception ParseError of string
exception TypeError of string
exception UnificationError of string
type analyze_error
  = ParseError of string
  | TypeError of string
  | UnificationError of string

let rec analyse gensym_state node (env: (string * Type.t) list) non_generic: Type.t =
  match node with
  | Expr.Ident name -> get_type gensym_state name env non_generic
  | Expr.Apply (fn, arg) ->
     let fun_type = analyse gensym_state fn env non_generic in
     let arg_type = analyse gensym_state arg env non_generic in
     let result_type_param = Type.TyVar (TypeVariable.create gensym_state) in
     unify gensym_state (Function.create arg_type result_type_param) fun_type;
     result_type_param
  | Expr.Lambda (v, body) ->
     let arg_type = TypeVariable.create gensym_state in
     let arg_type_param = Type.TyVar arg_type in
     (* let new_env = StringMap.add v arg_type_param env in *)
     let new_env = (v, arg_type_param) :: env in
     let new_non_generic = TVSet.add arg_type non_generic in
     let result_type = analyse gensym_state body new_env new_non_generic in
     Function.create arg_type_param result_type
  | Expr.Let (v, defn, body) ->
     let defn_type = analyse gensym_state defn env non_generic in
     (* let new_env = StringMap.add v defn_type env in *)
     let new_env = (v, defn_type) :: env in
     analyse gensym_state body new_env non_generic
  | Expr.Letrec (v, defn, body) ->
     let new_type = TypeVariable.create gensym_state in
     let new_type_param = Type.TyVar new_type in
     (* let new_env = StringMap.add v new_type_param env in *)
     let new_env = (v, new_type_param) :: env in
     let new_non_generic = TVSet.add new_type non_generic in
     let defn_type = analyse gensym_state defn new_env new_non_generic in
     unify gensym_state new_type_param defn_type;
     analyse gensym_state body new_env non_generic
  | Expr.None -> assert false
  | Expr.U8 _n ->
    my_U8
  | Expr.Annotation (expected_typ, given_expr) ->
    let given_expr_type = analyse gensym_state given_expr env non_generic in
    unify gensym_state expected_typ given_expr_type;
    given_expr_type
  | Expr.String _s -> my_String
  | Expr.Unit -> my_Unit
  | Expr.Vector xs ->
    let new_type = TypeVariable.create gensym_state in
    let new_type_param = Type.TyVar new_type in
    let xs_types = (List.map (fun expr -> analyse gensym_state expr env non_generic) xs) in
    List.iter (fun ty ->
        unify gensym_state new_type_param ty;)
      (xs_types);
    my_Vector new_type_param
  | Expr.Dict key_value_pairs ->
    let keys = List.map fst key_value_pairs in
    let values = List.map snd key_value_pairs in
    let unify_many (xs: Expr.t list): Type.t =
      let new_type = TypeVariable.create gensym_state in
      let new_type_param = Type.TyVar new_type in
      let xs_types = (List.map (fun expr -> analyse gensym_state expr env non_generic) xs) in
      List.iter (fun ty ->
        unify gensym_state new_type_param ty;)
        (xs_types);
      new_type_param
    in
    my_Dict (unify_many keys) (unify_many values)

and string_of_context env =
  let rec inner acc = function
    | (name, typ) :: rest ->
       inner ("(" ^ name ^ " " ^ (Type.to_string env typ) ^ ")") rest
    | [] -> acc ^ ")"
  in inner "("

and context_contains_constructor context name =
  let rec search = function
    | (_ctor_name, Type.TyTagUnion ctors) :: rest ->
       if List.mem_assoc name ctors
       then true
       else search rest
    | (_, _) :: rest -> search rest
    | [] -> false
  in search context

and find_enum_matching_ctor context name =
  let rec search = function
    | (_ctor_name, Type.TyTagUnion ctors) :: rest ->
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
  else raise (ParseError ("Undefined symbol " ^ name))

and fresh global_env t non_generic: Type.t =
  let mappings = Hashtbl.create 30 in
  let rec freshrec tp: Type.t =
    let p = prune tp in
    match p with
    | Type.TyVar tv ->
       let non_generic_list =
         List.map (fun a -> Type.TyVar a) (TVSet.elements non_generic) in
       if is_generic tv non_generic_list
       then begin
           if not (Hashtbl.mem mappings p)
           then Hashtbl.replace mappings p (Type.TyVar (TypeVariable.create global_env));
           Hashtbl.find mappings p
         end
       else p
    | Type.TyTag (name, child_type) ->
       Type.TyTag (name, freshrec child_type)
    | Type.TyTagUnion child_types ->
       Type.TyTagUnion (List.map
                          (fun (name, x) -> (name, freshrec x))
                          child_types)
    | Type.TyOp (name, child_types) ->
       Type.TyOp (TypeOperator.create
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
  | (Type.TyVar tyvar, _) ->
     if a <> b
     then begin
         if occurs_in_type tyvar b
         then raise (TypeError "recursive unification")
         else tyvar.TypeVariable.instance <- Some b
       end
  | (_ (* Type.TyOp(_top) *)
    , Type.TyVar _tyvar) ->
     unify gensym_state b a
  (* | (Type.TyOp (top1_name, top1_types), Type.TyTag (tytag_name, tytag_type)) -> *)
  (*
(let Maybe (enum (Maybe a) (Just a) None)
  (Maybe Just (u8 1)))
TyEnum ("Maybe", ty_var "a", [Ty])
 *)
  | (Type.TyOp (top1_name, top1_types), Type.TyOp (top2_name, top2_types)) ->
     (* Same names and arity *)
     let top1_types_size = (List.length top1_types) in
     let top2_types_size = (List.length top2_types) in
     (* JESPER! Här kollar vi att båda Terms eller Type Operators (TyOp) har samma namn och antal argument *)
     (* Med OR type operators aka terms, så måste vi istället kolla om den ena eller andra TypeOperator har label som en "child" av den andra. Detta för att "(Just a)" inte är = (Maybe a), men matchar child of (Maybe a).  *)
     if ((top1_name <> top2_name) || (top1_types_size <> top2_types_size))
     then raise (TypeError ("Type mismatch "
                            ^ (TypeOperator.to_string
                                 gensym_state
                                 (top1_name, top1_types))
                            ^ " != "
                            ^ (TypeOperator.to_string
                                 gensym_state
                                 (top2_name, top2_types))));
     (* Här kollar den bara om TypeOperators top1 och top2 är lika - men med OR behöver den också kolla om den ena är "child" till den andra, vilket är enkelt som att kolla om List.contains i den ena eller andras children. Kom ihåg, en typ = Sym of string | TypeOperator of string * typ list | TypeOperatorOr of string * typ list.

Så (Maybe a) => (TypeOperatorOr "Maybe" [Sym "a"])
Och (Just a) => (TypeOperator "Just" [Sym "a"])
unify (Maybe a) (Just b) => (Maybe a)*)
     List.iter2 (unify gensym_state) (top1_types) (top2_types)
(* | _ -> raise (UnificationError "Not unified") *)
  | (Type.TyTagUnion (cases), Type.TyTag (tag_name, tag_typ))|
    (Type.TyTag (tag_name, tag_typ), Type.TyTagUnion (cases))->
     (match List.assoc_opt tag_name cases with
      | Some canonical_typ ->
         (* canonical type is what we expect - it should unify with tag_type *)
         unify gensym_state canonical_typ tag_typ
      | None -> raise (TypeError ("Union Tag mismatch "
                                  ^ Type.to_string gensym_state (Type.TyTagUnion (cases))
                                  ^ "not matching "
                                  ^ Type.to_string gensym_state tag_typ)))
  | (Type.TyOp (_, _), (Type.TyTag _|TyTagUnion _))|
      ((TyTag _|TyTagUnion _), TyOp (_, _)) ->
     raise (TypeError ("TyOp and TyTag|TyTagUnion don't unify"))
  | (Type.TyTag (t1_name, t1_typ), Type.TyTag (t2_name, t2_typ)) ->
     if t1_name = t2_name
     then unify gensym_state t1_typ t2_typ
     else raise (TypeError "Given two TyTag but they are not of the same tag name")
  | (TyTagUnion _, (TyTagUnion _)) ->
     unify gensym_state a b

and prune (t: Type.t) =
  match t with
  | Type.TyVar tv ->
     (match tv.TypeVariable.instance with
      | Some stv ->
         tv.TypeVariable.instance <- Some (prune stv);
         stv
      | None -> t)
  | _ -> t

and is_generic (v: TypeVariable.t) non_generic = not (occurs_in v non_generic)

and occurs_in_type (v: TypeVariable.t) t2 =
  let pruned_t2 = prune t2 in
  match pruned_t2 with
  | Type.TyVar tv when tv = v -> true
  | Type.TyOp  (_name, tyop_types) -> occurs_in v tyop_types
  | _ -> false

and occurs_in (t: TypeVariable.t) types = List.exists (fun t2 -> occurs_in_type t t2) types

and is_integer_literal name =
  try ignore (int_of_string name);
      true
  with Failure _ -> false

let try_exp global_env env node =
  Printf.printf "%s: " (Expr.to_string global_env node);
  try print_endline (Type.to_string
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
       (let global_env = new_env () in
        (analyse
           global_env
           (Expr.Lambda ("x"
                       , (Expr.Lambda
                            ("y"
                            , Expr.Ident "x"))))
           []
           TVSet.empty)) in
     Printf.sprintf
       "type of K combinator is (-> a b a), actually: %s"
       (Type.to_string
          (new_env ())
          actually)
   , actually
     = (Type.TyOp
          ("->",
           [Type.TyVar {TypeVariable.id = 0; name = ""; instance = None};
            Type.TyOp
              ("->",
               [Type.TyVar {TypeVariable.id = 1; name = ""; instance = None};
                Type.TyVar {TypeVariable.id = 0; name = ""; instance = None}])])))]

    (* let () =
 *   let var1 = Type.TyVar (TypeVariable.create ()) in
 *   let var2 = Type.TyVar (TypeVariable.create ()) in
 *   let pair_type = Type.TyOp (TypeOperator.create "*" [var1; var2]) in
 *   let var3 = Type.TyVar (TypeVariable.create ()) in
 *   let my_env =
 *     StringMap.empty
 *     |> StringMap.add "pair" (Function.create var1 (Function.create var2 pair_type))
 *     |> StringMap.add "true" my_bool
 *     |> StringMap.add "cond"
 *          (Function.create my_bool
 *             (Function.create var3
 *                (Function.create var3 var3)))
 *     |> StringMap.add "zero" (Function.create my_int my_bool)
 *     |> StringMap.add "pred" (Function.create my_int my_int)
 *     |> StringMap.add "times" (Function.create my_int (Function.create my_int my_int))
 *   in let pair =
 *        (Expr.Apply
 *           ((Expr.Apply
 *               ((Expr.Ident "pair"),
 *                (Expr.Apply
 *                   ((Expr.Ident "f"), (Expr.Ident "4")))),
 *             (Expr.Apply
 *                ((Expr.Ident "f"),
 *                 (Expr.Ident "true"))))))
 *      in let examples =
 *           [
 *             (\* factorial *\)
 *             (Expr.Letrec              (\* letrec factorial = *\)
 *                ("factorial",
 *                 Expr.Lambda           (\* fun n -> *\)
 *                   ("n",
 *                    Expr.Apply (
 *                        Expr.Apply (     (\* cond (zero n) 1 *\)
 *                            Expr.Apply     (\* cond (zero n) *\)
 *                              (Expr.Ident "cond",
 *                               Expr.Apply (Expr.Ident "zero", Expr.Ident "n")),
 *                            Expr.Ident "1"),
 *                        Expr.Apply (     (\* times n *\)
 *                            Expr.Apply (Expr.Ident "times", Expr.Ident "n"),
 *                            Expr.Apply (
 *                                Expr.Ident "factorial",
 *                                Expr.Apply (Expr.Ident "pred", Expr.Ident "n")
 *                   )))),          (\* in *\)
 *                 Expr.Apply (Expr.Ident "factorial", Expr.Ident "5")));
 *
 *             (\* Should fail
 *              * fun x -> (pair (x 3) (x true))
 *              *\)
 *             Expr.Lambda("x",
 *                         Expr.Apply(
 *                             Expr.Apply(Expr.Ident "pair",
 *                                        Expr.Apply(Expr.Ident "x", Expr.Ident "3")),
 *                             Expr.Apply(Expr.Ident "x", Expr.Ident "true")));
 *
 *             (\* (pair (f 3)) (f true) *\)
 *             Expr.Apply(
 *                 Expr.Apply(Expr.Ident "pair", Expr.Apply(Expr.Ident "f", Expr.Ident "4")),
 *                 Expr.Apply(Expr.Ident "f", Expr.Ident "true"));
 *
 *             (\* let f = (fn x -> x) in ((pair (f 4)) (f true)) *\)
 *             Expr.Let("f", Expr.Lambda("x", Expr.Ident "x"), pair);
 *
 *             (\* fun f -> f f *\)
 *             (\* This should fail (recursive type definition) *\)
 *             Expr.Lambda("f", Expr.Apply(Expr.Ident "f", Expr.Ident "f"));
 *
 *             (\* let g = fun f -> 5 in g g *\)
 *             Expr.Let("g", Expr.Lambda("f", Expr.Ident "5"),
 *                      Expr.Apply(Expr.Ident "g", Expr.Ident "g"));
 *
 *             (\* example that demonstrates generic and non-generic variables *\)
 *             (\* fun g -> let f = fun x -> g in pair (f 3, f true) *\)
 *             Expr.Lambda("g",
 *                         Expr.Let("f",
 *                                  Expr.Lambda("x", Expr.Ident "g"),
 *                                  Expr.Apply(
 *                                      Expr.Apply(
 *                                          Expr.Ident "pair",
 *                                          Expr.Apply(Expr.Ident "f", Expr.Ident "3")),
 *                                      Expr.Apply(Expr.Ident "f", Expr.Ident "true"))));
 *
 *             (\* function composition *\)
 *             (\* fun f -> fun g -> fun arg -> f g arg *\)
 *             Expr.Lambda("f",
 *                         Expr.Lambda("g",
 *                                     Expr.Lambda("arg",
 *                                                 Expr.Apply(
 *                                                     Expr.Ident "g",
 *                                                     Expr.Apply(
 *                                                         Expr.Ident "f",
 *                                                         Expr.Ident "arg")))))
 *
 *
 *           ]
 *         in
 *         List.iter (fun ex -> try_exp my_env ex) examples *)
