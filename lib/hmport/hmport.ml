(* type 'expr lambda = string * 'expr
 *
 * type atom =
 *   | Number of int
 *   | Bool of bool
 *
 * let string_of_atom = function
 *   | Number n -> string_of_int n
 *   | Bool b -> string_of_bool b
 *
 *
 * type expr =
 *   | App of expr * expr
 *   | Var of string
 *   | Lam of expr lambda
 *   | Let of string * expr * expr
 *   | Atom of atom
 *
 * let string_of_expr = function
 *   | App (_, _) -> "App"
 *   | Var s -> s
 *   | Lam (_x, _body) -> "Lam"
 *   | Let (_, _, _) -> "Let"
 *   | Atom a -> string_of_atom a *)

let union = List.append

let disj list x =
  let rec inner list x acc =
    match list with
    | [] -> acc
    | x' :: rest ->
      let acc = if x = x' then acc else x' acc in
      inner rest x acc
  in
  inner list x []


module VarSet = Set.Make (String)

let rec free_vars (expr : Expr.expr) =
  match expr with
  | U8 (_, _) -> VarSet.empty
  | String (_, _) -> VarSet.empty
  | Unit _ -> VarSet.empty
  | Sym (_, s) -> VarSet.add s VarSet.empty
  | App (_, f, x) -> VarSet.union (free_vars f) (free_vars x)
  | Lam (_, (PSym (_, x), body) :: _) ->
    VarSet.filter (( = ) x) (free_vars body)
  | Lam (_, (PTag (_, _, _), _) :: _) -> failwith "PTag free_vars not done"
  | Lam (_, []) -> failwith "PTag free_vars not done"
  | Let (_, var, value, body) ->
    let vars = VarSet.add var VarSet.empty in
    let vals = [ value ] in
    let vals_free_vals =
      List.fold_left VarSet.union (free_vars body) (List.map free_vars vals)
    in
    VarSet.diff vals_free_vals vars
  | Tuple (_, _)
  | Vector (_, _)
  | Set (_, _)
  | Dict (_, _)
  | Ann (_, _, _)
  | Match (_, _, _)
  | Letrec (_, _, _, _)
  | TaggedValue (_, _, _)
  | Enum _
  | TypeDef (_, _, _) ->
    failwith "Haven't implemented free_vars of fancy expressions"


type constant =
  | Integer
  | String
  | Arrow
  | Boolean
  | Unit

let string_of_constant = function
  | Integer -> "Integer"
  | String -> "String"
  | Arrow -> "->"
  | Boolean -> "Boolean"
  | Unit -> "Unit"


type typ =
  | TypeConstant of constant
  | TypeVariable of string
  | TypeApp of typ list
  (* (forall [a b] (-> a b a)) *)
  | TypeScheme of string list * typ list

let remove_from_list (list : 'a list) (search : 'a) =
  let rec inner list acc =
    match list with
    | [] -> List.rev acc
    | x :: xs -> inner xs (if x = search then acc else x :: acc)
  in
  inner list []


let rec string_of_typ = function
  | TypeConstant c -> string_of_constant c
  | TypeVariable s -> "(TVar " ^ s ^ ")"
  | TypeApp ts -> "(" ^ String.concat " " (List.map string_of_typ ts) ^ ")"
  (* (forall [a b] (-> a b a)) *)
  | TypeScheme (args, body) ->
    "(forall ["
    ^ String.concat " " args
    ^ " "
    ^ String.concat " " (List.map string_of_typ body)
    ^ ")"


let gen_type_variable_state = ref 0

let split_first s query =
  Printf.printf "split_first %s %s\n" s query;
  if s = ""
  then ""
  else
    let rec inner s query index =
      if index > String.length query
      then
        if String.sub s index (String.length query) = query
        then String.sub s 0 index
        else inner s query (index + 1)
      else s
    in
    inner s query 0


(* TODO this is stringly typed - ideally, a variable would be a pair of strings,
   where the second item is the postfix. Thus not requiring __ to be a special
   modifier *)
let gen_type_variable x =
  (* Port of clojure.core/gensym *)
  let x = if x = "" then "G" else x in
  let name = split_first x "__" in
  TypeVariable (name ^ "__" ^ string_of_int !gen_type_variable_state)


let zipmap = List.combine

(* module TypSet = Set.Make (typ) *)

let rec replace_substitutions (substitutions : (string * typ) list) (t : typ) :
    typ =
  match t with
  | TypeConstant _c -> t
  | TypeVariable name ->
    ( match List.assoc_opt name substitutions with
    | Some t -> t
    | None -> t )
  | TypeApp [] -> TypeApp []
  | TypeApp type_functors ->
    TypeApp (List.map (replace_substitutions substitutions) type_functors)
  | TypeScheme (args, xs) ->
    (* TODO should I also replace the args? *)
    TypeScheme (args, List.map (replace_substitutions substitutions) xs)


type typ_env = (string * typ) list

let replace_substitutions_env
    (substitutions : (string * typ) list) (env : typ_env) =
  List.map (fun (name, t) -> (name, replace_substitutions substitutions t)) env


let instantiate t =
  match t with
  | TypeScheme (vars, t') ->
    let substitutions = zipmap vars (List.map gen_type_variable vars) in
    TypeApp (List.map (replace_substitutions substitutions) t')
  | _ -> t


let difference l1 l2 = List.filter (fun x -> not (List.mem x l2)) l1

(* invariant: treats typ list as if it was a set *)
let rec free_types (x : typ) : typ list =
  match x with
  | TypeConstant _c -> []
  | TypeVariable _v -> [ x ]
  | TypeApp (_n :: types) -> List.fold_left union [] (List.map free_types types)
  | TypeApp [] -> failwith "Not sure what to do here"
  | TypeScheme (vars, t) ->
    difference
      (free_types (TypeApp t))
      (List.map (fun v -> TypeVariable v) vars)


let rec free_type_vars (x : typ) : string list =
  match x with
  | TypeConstant _c -> []
  | TypeVariable v -> [ v ]
  | TypeApp (_n :: types) ->
    List.fold_left union [] (List.map free_type_vars types)
  | TypeApp [] -> failwith "Not sure what to do here"
  | TypeScheme (vars, t) ->
    difference (free_type_vars (TypeApp t)) (List.map (fun v -> v) vars)


let free_type_vars_env (env : typ_env) : string list =
  List.flatten (List.map (fun (_name, t) -> free_type_vars t) env)


let vbind (v : string) (t : typ) : typ_env =
  if List.mem (TypeVariable v) (free_types t)
  then failwith "Recursive unification."
  else [ (v, t) ]


let merge_alist l0 l1 =
  List.fold_left
    (fun list (key, value) -> (key, value) :: List.remove_assoc key list)
    l0
    l1


let val_map f = List.map (fun (k, v) -> (k, f v))

let compose_substitutions (a : typ_env) (b : typ_env) : typ_env =
  merge_alist (val_map (replace_substitutions a) b) a


let rec unify (t1 : typ) (t2 : typ) : typ_env =
  Printf.printf "unify t1: %s t2: %s\n" (string_of_typ t1) (string_of_typ t2);
  if t1 = t2
  then []
  else
    match (t1, t2) with
    | TypeApp (n1 :: ts1), TypeApp (n2 :: ts2) ->
      if not (n1 = n2)
      then
        failwith
          ( "Cannot unify two different type applications: "
          ^ string_of_typ n1
          ^ " and "
          ^ string_of_typ n2 )
      else if not (List.length ts1 = List.length ts2)
      then
        failwith
          ( "Cannot unify two type applications with different numbers of \
             types: "
          ^ string_of_typ t1
          ^ " & "
          ^ string_of_typ t2 )
      else
        List.fold_left
          (fun substitutions (t1, t2) ->
            let t1 : typ = t1 in
            let t2 : typ = t2 in
            let substitutions2 =
              unify
                (replace_substitutions substitutions t1)
                (replace_substitutions substitutions t2)
            in
            compose_substitutions substitutions2 substitutions )
          []
          (List.map2 (fun x y -> (x, y)) ts1 ts2)
    | TypeVariable t1, _x -> vbind t1 t2
    | _, TypeVariable t2 -> vbind t2 t1
    | _ ->
      failwith ("Types do not unify: " ^ string_of_typ t1 ^ string_of_typ t2)


(* Convert a type into a type scheme by converting free type variables into
   existential variables. Has no effect if there are no free variables. *)
let generalize (env : typ_env) (t : typ) =
  match t with
  | TypeApp body ->
    let vars : string list =
      difference (free_type_vars t) (free_type_vars_env env)
    in
    if List.length vars > 0 then TypeScheme (vars, body) else t
  | _ -> t


let rec infer_type (env : typ_env) (exp : Expr.expr) : typ_env * typ =
  match exp with
  | Match (_, _, _)
  | Letrec (_, _, _, _)
  | TaggedValue (_, _, _)
  | Enum _
  | TypeDef (_, _, _) ->
    failwith "A bunch of type inferrence things not done"
  | Ann (_, _t, _e) -> failwith "Annotation inferrence not implemented"
  | U8 (_, _) -> ([], TypeConstant Integer)
  | String (_, _) -> ([], TypeConstant String)
  | Unit (_, _) -> ([], TypeConstant Unit)
  | Tuple (_, _children) ->
    failwith "haven't yet implemented typecheck for tuples"
  | Vector (_, _children) ->
    failwith "haven't yet implemented typecheck for vectors"
  | Set (_, _children) -> failwith "haven't yet implemented typecheck for sets"
  | Dict (_, _children) ->
    failwith "haven't yet implemented typecheck for dicts"
  | Sym (_, v) ->
    ( match List.assoc_opt v env with
    | Some t -> ([], instantiate t)
    | None ->
      let _state, expr_string = Expr.string_of_expr (-1, 'a') exp in
      failwith ("Unbound variable: " ^ expr_string) )
  | Lam (_pos, (PSym (_, arg), body) :: _) ->
    let arg_t = gen_type_variable arg in
    let env' = (arg, arg_t) :: env in
    let substitutions, body_t = infer_type env' body in
    ( substitutions
    , replace_substitutions
        substitutions
        (TypeApp [ TypeConstant Arrow; arg_t; body_t ]) )
  | Lam (_, []) -> failwith "Can't check a lambda without cases?"
  | Lam (_, (PTag (_, _, _), _) :: _) -> failwith "not done"
  | App (_, fn, arg) ->
    let res_t =
      match fn with
      | Sym (_, fn_name) -> gen_type_variable (fn_name ^ "-result")
      | _ -> gen_type_variable ""
    in
    let substs1, fun_t = infer_type env fn in
    let substs2, arg_t =
      infer_type (replace_substitutions_env substs1 env) arg
    in
    let subst3 =
      unify
        (replace_substitutions substs2 fun_t)
        (TypeApp [ TypeConstant Arrow; arg_t; res_t ])
    in
    ( List.fold_left compose_substitutions subst3 [ substs2; substs1 ]
    , replace_substitutions subst3 res_t )
  | Let (_, var, value, body) ->
    if VarSet.mem var (free_vars value)
    then
      let tv = gen_type_variable var in
      let env' = (var, tv) :: env in
      let s1, t1 = infer_type env' value in
      let s1' = unify tv t1 in
      let s2, t2 =
        infer_type
          (replace_substitutions_env (compose_substitutions s1 s1') env')
          body
      in
      (compose_substitutions s2 s1, t2)
    else
      let s1, t1 = infer_type env value in
      let t' = generalize (replace_substitutions_env s1 env) t1 in
      let env' = (var, t') :: env in
      let s2, t2 = infer_type (replace_substitutions_env s1 env') body in
      (compose_substitutions s2 s1, t2)


let infer env exp =
  match Ok (infer_type env exp) with
  | Ok (substitutions, t) ->
    generalize env (replace_substitutions substitutions t)
  | _ -> failwith "infer_type error"
