module Expr = struct
  type t =
    | Ident of string
    | Apply of t * t
    | Lambda of string * t
    | Let of string * t * t
    | Letrec of string * t * t
    | None
    | U8 of int
    | Annotation of t * t

  let rec from_read_expr read_expr =
    match read_expr with
    | Read.Lam (_pos, (PSym (_psym_pos, pattern), expr) :: _pattern_expr_rest) ->
       Lambda (pattern, from_read_expr expr)
    | Lam (_pos, _patterns_exprs) ->
       failwith "Currently I can only convert Lam with a PSym"
    | App (_pos, Sym (_, "Log"), _e1) ->
       failwith "Can't yet type check Commands"
    | App (_pos, e0, e1) ->
       Apply (from_read_expr e0, from_read_expr e1)
    | Sym (_pos, x) ->
       Ident x
    | U8 (_pos, n) -> U8 n
    | String (_pos, _text) -> failwith "from of String not possible"
    | Tuple (_pos, _exprs) -> failwith "from of Tuple not possible"
    | Unit _pos -> failwith "from of Unit not possible"
    | Vector (_pos, _exprs) -> failwith "from of Vector not possible"
    | Set (_pos, _exprs) -> failwith "from of Set not possible"
    | Ann (_pos, _t, _expr) -> failwith "from of Ann not possible"
    | Dict (_pos, _exprs) -> failwith "from of Dict not possible"
    | Match (_pos, _x, _patterns_exprs) -> failwith "from of Match not possibl"

  let rec to_string = function
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
    | Annotation (t, expr) -> Printf.sprintf "(Ann %s %s)"
                                (to_string t)
                                (to_string expr)
end

let rec pow a = function
  | 0 -> 1
  | 1 -> a
  | n -> let b = pow a (n / 2) in
         b * b * (if n mod 2 = 0 then 1 else a)

type env =
  { mutable next_variable_id : int
  ; mutable next_variable_name : char }

let global_env = {next_variable_id = 0
                 ;next_variable_name = 'a'}

module rec TypeVariable : sig
         type t = { id: int
                  ; mutable name: string
                  ; mutable instance: TypeParameter.t option }
         val create: unit -> t
         val name: t -> string
         val to_string: t -> string
         val compare: t -> t -> int
         val hash: t -> int
         val equal: t -> t -> bool
       end = struct
  type t = {id: int
           ;mutable name: string
           ;mutable instance: TypeParameter.t option }
  let create () = global_env.next_variable_id <- global_env.next_variable_id + 1;
                  { id = global_env.next_variable_id - 1
                  ; name = ""
                  ; instance = None }
  let name tv =
    if tv.name = ""
    then begin
        tv.name <- Char.escaped global_env.next_variable_name;
        global_env.next_variable_name <- Char.chr ((Char.code global_env.next_variable_name) + 1)
      end;
    tv.name

  let to_string tv =
    match tv.instance with
    | None -> name tv
    | Some i -> TypeParameter.to_string i

  let compare t1 t2 = t2.id - t1.id
  let hash tv = tv.id
  let equal tv1 tv2 = tv1.id = tv2.id
end

   and TypeOperator: sig
     type t = { name: string; types: TypeParameter.t list}
     val create: string -> TypeParameter.t list -> t
     val to_string: t -> string
   end = struct
     type t = { name : string
              ; types: TypeParameter.t list}
     let create n tl = { name = n
                       ; types = tl }
     let to_string t = match t.types with
       | [] -> t.name
       | hd::tl::[] ->
          Printf.sprintf "(%s %s %s)" (TypeParameter.to_string hd) t.name (TypeParameter.to_string tl)
       | _ -> t.types
              |> List.map TypeParameter.to_string
              |> List.fold_left (fun a b -> a ^ " " ^ b) ""
              |> Printf.sprintf "%s %s" t.name

     (* let compare top1 top2 = compare top1.types top2.types *)
     (* let hash tv =
      *   let rec hash' p = function
      *     | t::tl ->
      *        (pow 31 p) + (TypeVariable.hash t) + (hash' (p + 1) tl)
      *     | [] -> 0
      *   in
      *   hash' 0 tv.types *)
   end

   and TypeParameter: sig
     type t = TypeParam_tvar of TypeVariable.t
            | TypeParam_top of TypeOperator.t
     val to_string: t -> string
   end = struct
     type t =
       | TypeParam_tvar of TypeVariable.t
       | TypeParam_top of TypeOperator.t
     let to_string = function
       | TypeParam_tvar tv -> TypeVariable.to_string tv
       | TypeParam_top top -> TypeOperator.to_string top
   end

   and Function: sig
     val create: TypeParameter.t -> TypeParameter.t -> TypeParameter.t
   end = struct
     let create from_type to_type =
       TypeParameter.TypeParam_top
         { TypeOperator.name = "->"
         ; TypeOperator.types = [from_type; to_type] }
   end

let rec zip xl yl =
  match (xl, yl) with
  | (x::xs, y::ys) -> (x, y) :: zip xs ys
  | ([], []) -> []
  | _ -> assert false

(*  Basic types are constructed with a nullary type constructor  *)
let my_U8 =
  (let arg_type = TypeVariable.create () in
   let arg_type_param = TypeParameter.TypeParam_tvar arg_type in
   Function.create arg_type_param (TypeParameter.TypeParam_tvar
                                     (TypeVariable.create ()))
  )
(* (TypeOperator.create "U8" []) *)
(* let my_String = TypeParameter.TypeParam_top (TypeOperator.create "String" []) *)
let my_String = (let arg_type = TypeVariable.create () in
                 let arg_type_param = TypeParameter.TypeParam_tvar arg_type in
                 Function.create arg_type_param (TypeParameter.TypeParam_tvar
                                                   (TypeVariable.create ()))
                )
let my_Bool = TypeParameter.TypeParam_top (TypeOperator.create "Bool" [])
let my_Int = TypeParameter.TypeParam_top (TypeOperator.create "String" [])
(* let my_Any () = TypeParameter.TypeParam_tvar (TypeVariable.create ()) *)

module TVSet = Set.Make(TypeVariable)
module StringMap = Map.Make(String)

exception ParseError of string
exception TypeError of string
exception UnificationError of string

let rec analyse node env non_generic: TypeParameter.t =
  match node with
  | Expr.Ident name -> get_type name env non_generic
  | Expr.Apply (fn, arg) ->
     let fun_type = analyse fn env non_generic in
     let arg_type = analyse arg env non_generic in
     let result_type = TypeVariable.create () in
     let result_type_param = TypeParameter.TypeParam_tvar result_type in
     unify (Function.create arg_type result_type_param) fun_type;
     result_type_param
  | Expr.Lambda (v, body) ->
     let arg_type = TypeVariable.create () in
     let arg_type_param = TypeParameter.TypeParam_tvar arg_type in
     let new_env = StringMap.add v arg_type_param env in
     let new_non_generic = TVSet.add arg_type non_generic in
     let result_type = analyse body new_env new_non_generic in
     Function.create arg_type_param result_type
  | Expr.Let (v, defn, body) ->
     let defn_type = analyse defn env non_generic in
     let new_env = StringMap.add v defn_type env in
     analyse body new_env non_generic
  | Expr.Letrec (v, defn, body) ->
     let new_type = TypeVariable.create () in
     let new_type_param = TypeParameter.TypeParam_tvar new_type in
     let new_env = StringMap.add v new_type_param env in
     let new_non_generic = TVSet.add new_type non_generic in
     let defn_type = analyse defn new_env new_non_generic in
     unify new_type_param defn_type;
     analyse body new_env non_generic
  | Expr.None -> assert false
  | Expr.U8 _n ->
     let arg_type = TypeVariable.create () in
     let arg_type_param = TypeParameter.TypeParam_tvar arg_type in
     Function.create arg_type_param (TypeParameter.TypeParam_tvar
                                       (TypeVariable.create ()))
  | Expr.Annotation (_t, _expr) ->
     failwith "Can't do this Ann..."

and get_type name env non_generic =
  if StringMap.mem name env
  then fresh (StringMap.find name env) non_generic
  else if is_integer_literal name
  then my_U8
  else raise (ParseError ("Undefined symbol " ^ name))
and fresh t non_generic: TypeParameter.t =
  let mappings = Hashtbl.create 30 in
  let rec freshrec tp: TypeParameter.t =
    let p = prune tp in
    match p with
    | TypeParameter.TypeParam_tvar tv ->
       let non_generic_list =
         List.map (fun a -> TypeParameter.TypeParam_tvar a) (TVSet.elements non_generic) in
       if is_generic tv non_generic_list
       then begin
           if not (Hashtbl.mem mappings p)
           then Hashtbl.replace mappings p (TypeParameter.TypeParam_tvar (TypeVariable.create ()));
           Hashtbl.find mappings p
         end
       else p
    | TypeParameter.TypeParam_top(top) ->
       TypeParameter.TypeParam_top (TypeOperator.create top.TypeOperator.name
                                      (List.map (fun x -> freshrec x) top.TypeOperator.types))
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
and unify t1 t2: unit =
  let a = prune t1 in
  let b = prune t2 in
  match (a, b) with
  | (TypeParameter.TypeParam_tvar(tv), _) ->
     if a <> b
     then begin
         if occurs_in_type tv b
         then raise (TypeError "recursive unification")
         else tv.TypeVariable.instance <- Some b
       end
  | (TypeParameter.TypeParam_top(_top), TypeParameter.TypeParam_tvar(_tv)) ->
     unify b a
  | (TypeParameter.TypeParam_top(top1), TypeParameter.TypeParam_top(top2)) ->
     (* Same names and arity *)
     let top1_name = top1.TypeOperator.name in
     let top2_name = top2.TypeOperator.name in
     let top1_types_size = (List.length top1.TypeOperator.types) in
     let top2_types_size = (List.length top2.TypeOperator.types) in
     (* JESPER! Här kollar vi att båda Terms eller Type Operators (TypeParam_top) har samma namn och antal argument *)
     (* Med OR type operators aka terms, så måste vi istället kolla om den ena eller andra TypeOperator har label som en "child" av den andra. Detta för att "(Just a)" inte är = (Maybe a), men matchar child of (Maybe a).  *)
     if ((top1_name <> top2_name) || (top1_types_size <> top2_types_size))
     then raise (TypeError ("Type mismatch " ^ (TypeOperator.to_string top1) ^ " != " ^ (TypeOperator.to_string top2)));
     (* Här kollar den bara om TypeOperators top1 och top2 är lika - men med OR behöver den också kolla om den ena är "child" till den andra, vilket är enkelt som att kolla om List.contains i den ena eller andras children. Kom ihåg, en typ = Sym of string | TypeOperator of string * typ list | TypeOperatorOr of string * typ list.

Så (Maybe a) => (TypeOperatorOr "Maybe" [Sym "a"])
Och (Just a) => (TypeOperator "Just" [Sym "a"])
unify (Maybe a) (Just b) => (Maybe a)*)
     List.iter2 unify (top1.TypeOperator.types) (top2.TypeOperator.types)
(* | _ -> raise (UnificationError "Not unified") *)

and prune (t: TypeParameter.t) =
  match t with
  | TypeParameter.TypeParam_tvar tv ->
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
  | TypeParameter.TypeParam_tvar tv when tv = v -> true
  | TypeParameter.TypeParam_top top -> occurs_in v top.TypeOperator.types
  | _ -> false

and occurs_in (t: TypeVariable.t) types = List.exists (fun t2 -> occurs_in_type t t2) types

and is_integer_literal name =
  try ignore (int_of_string name);
      true
  with Failure _ -> false

let try_exp env node =
  Printf.printf "%s: " (Expr.to_string node);
  try print_endline (TypeParameter.to_string (analyse node env TVSet.empty))
  with
  | ParseError e | TypeError e ->
     print_endline e

let analyze_result env node =
  try Ok (analyse node env TVSet.empty)
  with
  | ParseError e -> Error (ParseError e)
  | TypeError e -> Error (TypeError e)

let type_infer_tests =
  [( Printf.sprintf "type of K combinator is (-> a b a), actually: %s"
       (TypeParameter.to_string (analyse
                                   (Expr.Lambda ("x"
                                               , (Expr.Lambda
                                                    ("y"
                                                    , Expr.Ident "x"))))
                                   StringMap.empty TVSet.empty))
   , analyse (Expr.Lambda ("x", (Expr.Lambda ("y", Expr.Ident "x")))) StringMap.empty TVSet.empty
     = TypeParameter.TypeParam_top
         {TypeOperator.name = "->";
          types =
            [TypeParameter.TypeParam_tvar
               {TypeVariable.id = 4; name = ""; instance = None};
             TypeParameter.TypeParam_top
               {TypeOperator.name = "->";
                types =
                  [TypeParameter.TypeParam_tvar
                     {TypeVariable.id = 5; name = ""; instance = None};
                   TypeParameter.TypeParam_tvar
                     {TypeVariable.id = 4; name = ""; instance = None}]}]})]

(* let () =
 *   let var1 = TypeParameter.TypeParam_tvar (TypeVariable.create ()) in
 *   let var2 = TypeParameter.TypeParam_tvar (TypeVariable.create ()) in
 *   let pair_type = TypeParameter.TypeParam_top (TypeOperator.create "*" [var1; var2]) in
 *   let var3 = TypeParameter.TypeParam_tvar (TypeVariable.create ()) in
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
