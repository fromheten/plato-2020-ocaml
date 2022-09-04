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


type 'a constant =
  | Integer
  | String
  | Arrow
  | Boolean
  | Unit
  | Vector of 'a
  | Dict of 'a * 'a
[@@deriving show]

type typ =
  | TypeConstant of typ constant
  | TypeVariable of string
  | TypeApp of typ list
  (* (forall [a b] (-> a b a)) *)
  | TypeScheme of string list * typ list
[@@deriving show]

let rec string_of_constant = function
  | Integer -> "Integer"
  | String -> "String"
  | Arrow -> "->"
  | Boolean -> "Boolean"
  | Unit -> "Unit"
  (* | Vector child -> "[" ^ string_of_typ child ^ "]" *)
  | Vector child -> "(Vector " ^ string_of_typ child ^ ")"
  | Dict (key_t, value_t) ->
    "{" ^ string_of_typ key_t ^ " " ^ string_of_typ value_t ^ "}"


and string_of_typ = function
  | TypeConstant c -> string_of_constant c
  | TypeVariable s -> s
  | TypeApp ts -> "(" ^ String.concat " " (List.map string_of_typ ts) ^ ")"
  (* (forall [a b] (-> a b a)) *)
  | TypeScheme (args, body) ->
    "(forall ["
    ^ String.concat " " args
    ^ "] ("
    ^ String.concat " " (List.map string_of_typ body)
    ^ "))"


let remove_from_list (list : 'a list) (search : 'a) =
  let rec inner list acc =
    match list with
    | [] -> List.rev acc
    | x :: xs -> inner xs (if x = search then acc else x :: acc)
  in
  inner list []


let gen_type_variable_state = ref 0

let split_first s query =
  if s = ""
  then ""
  else
    let rec inner index =
      let query_len = String.length query in
      if index + query_len <= String.length s
      then
        if String.sub s index query_len = query
        then String.sub s 0 index
        else inner (index + 1)
      else s
    in
    let result = inner 0 in
    result


(* TODO this is stringly typed - ideally, a variable would be a pair of strings,
   where the second item is the postfix. Thus not requiring __ to be a special
   modifier *)
let gen_type_variable x =
  (* Port of clojure.core/gensym *)
  let x = if x = "" then "G" else x in
  let name = split_first x "__" in
  let result =
    TypeVariable (name ^ "__" ^ string_of_int !gen_type_variable_state)
  in
  gen_type_variable_state := !gen_type_variable_state + 1;
  result


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


type typ_env = (string * typ) list [@@deriving show]

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


type unify_err =
  | TypeAppOfDifferentFunctor of typ * typ
  | TypeAppDifferentAritiesGiven of typ * typ
  | NotUnifyable of typ * typ

let string_of_unify_err = function
  | TypeAppOfDifferentFunctor (n1, n2) ->
    "Cannot unify two different type applications: "
    ^ string_of_typ n1
    ^ " and "
    ^ string_of_typ n2
  | NotUnifyable (t1, t2) ->
    "Types do not unify: \n" ^ string_of_typ t1 ^ "\n " ^ string_of_typ t2
  | TypeAppDifferentAritiesGiven (t1, t2) ->
    "Cannot unify two type applications with different numbers of types: "
    ^ string_of_typ t1
    ^ " & "
    ^ string_of_typ t2


let rec unify (t1 : typ) (t2 : typ) : (typ_env, unify_err) result =
  if t1 = t2
  then Ok []
  else
    match (t1, t2) with
    | TypeApp (n1 :: ts1), TypeApp (n2 :: ts2) ->
      (* Util.debugprint
       *   "Unify inputs"
       *   [ ("n1", string_of_typ n1)
       *   ; ("ts1", String.concat "\n" (List.map string_of_typ ts1))
       *   ; ("n2", string_of_typ n2)
       *   ; ("ts2", String.concat "\n" (List.map string_of_typ ts2))
       *   ]; *)
      if not (n1 = n2)
      then Error (TypeAppOfDifferentFunctor (n1, t2))
      else if not (List.length ts1 = List.length ts2)
      then Error (TypeAppDifferentAritiesGiven (t1, t2))
      else
        Ok
          (List.fold_left
             (fun substitutions (t1, t2) ->
               let t1 : typ = t1 in
               let t2 : typ = t2 in
               let substitutions2 =
                 Util.unwrap (* TODO remove this *)
                   (unify
                      (replace_substitutions substitutions t1)
                      (replace_substitutions substitutions t2) )
                   (Util.comp
                      (( ^ ) "Unify typeapp branch: ")
                      string_of_unify_err )
               in

               compose_substitutions substitutions2 substitutions )
             []
             (List.map2 (fun x y -> (x, y)) ts1 ts2) )
    | TypeVariable t1, _x -> Ok (vbind t1 t2)
    | _, TypeVariable t2 -> Ok (vbind t2 t1)
    | TypeApp (_ :: _), TypeApp [] -> Error (NotUnifyable (t1, t2))
    | TypeApp (_ :: _), (TypeConstant _ | TypeScheme (_, _)) ->
      Error (NotUnifyable (t1, t2))
    | TypeApp [], (TypeConstant _ | TypeApp _ | TypeScheme (_, _)) ->
      Error (NotUnifyable (t1, t2))
    | TypeConstant (Vector t1_child), TypeConstant (Vector t2_child) ->
      unify t1_child t2_child
    | _ -> Error (NotUnifyable (t1, t2))


let rec unify_many
    (typs : typ list) (env_acc : typ_env) (errs_acc : unify_err list) :
    (typ_env, unify_err list) result =
  match typs with
  | [] when List.length errs_acc = 0 -> Ok env_acc
  | [] -> Error errs_acc
  | [ t0; t1 ] ->
    ( match unify t0 t1 with
    | Ok env -> unify_many [] (List.concat [ env; env_acc ]) errs_acc
    | Error e -> unify_many [] env_acc (e :: errs_acc) )
  | t0 :: t1 :: rest ->
    ( match unify t0 t1 with
    | Ok env -> unify_many (t1 :: rest) (List.concat [ env; env_acc ]) errs_acc
    | Error e -> unify_many (t1 :: rest) env_acc (e :: errs_acc) )
  | [ t ] -> unify_many [ t; gen_type_variable "" ] env_acc errs_acc


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


let tUnit = TypeConstant Unit

let tArrow t0 t1 = TypeApp [ TypeConstant Arrow; t0; t1 ]
