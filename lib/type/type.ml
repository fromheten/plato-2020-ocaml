type gensym_state =
  { mutable next_variable_id : int
  ; mutable next_variable_name : char }

let new_gensym_state () = {next_variable_id = 0
                          ;next_variable_name = 'a'}

module rec TypeVariable : sig
         type t = { id: int
                  ; mutable name: string
                  ; mutable instance: Type.t option }
         val create: gensym_state -> t
         val name: gensym_state -> t -> string
         val to_string: gensym_state -> t -> string
         val compare: t -> t -> int
         val hash: t -> int
         val equal: t -> t -> bool
       end = struct
  type t = {id: int
           ;mutable name: string
           ;mutable instance: Type.t option }
  let create gensym_state =
    gensym_state.next_variable_id <- gensym_state.next_variable_id + 1;
    { id = gensym_state.next_variable_id - 1
    ; name = ""
    ; instance = None }
  let name gensym_state tv =
    if tv.name = ""
    then begin
        tv.name <- Char.escaped gensym_state.next_variable_name;
        gensym_state.next_variable_name <- Char.chr ((Char.code gensym_state.next_variable_name) + 1)
      end;
    tv.name

  let to_string gensym_state tv =
    match tv.instance with
    | None -> name gensym_state tv
    | Some typ ->
       Type.to_string gensym_state typ

  let compare t1 t2 = t2.id - t1.id
  let hash tv = tv.id
  let equal tv1 tv2 = tv1.id = tv2.id
end

and Type : sig
  type t = TyVar of TypeVariable.t
         | TyTag of (string * t)
         | TyTagUnion of (string * t) list
         | TyOp of string * Type.t list (* name, types. Think unification algorithm! *)
  val to_string: gensym_state -> t -> string
end = struct
  type t = TyVar of TypeVariable.t
         | TyTag of (string * t)
         | TyTagUnion of (string * t) list
         | TyOp of string * Type.t list (* name, types. Think unification algorithm! *)
  let rec to_string gensym_state = function
    | TyVar tv -> TypeVariable.to_string gensym_state tv ^ "-" ^ string_of_int tv.id ^ tv.name
    | TyTag (tag, tagged_typ) ->
      "(" ^ tag ^ " " ^ to_string gensym_state tagged_typ ^ ")"
    | TyTagUnion cases ->
      "(union " ^ String.concat " " (List.map
                                       (to_string gensym_state)
                                       (List.map (fun x -> TyTag x) cases))
    | TyOp (name, types) ->
      (match types with
       | [] -> name
       | hd::tl::[] ->
         Printf.sprintf "(%s %s %s)"
           name
           (Type.to_string gensym_state hd)
           (Type.to_string gensym_state tl)
       | _ -> types
              |> List.map (Type.to_string gensym_state)
              |> List.fold_left (fun a b -> a ^ " " ^ b) ""
              |> Printf.sprintf "%s %s" name)
end

let tArrow from_type to_type = Type.TyOp ("->", [from_type; to_type])
let tU8 = Type.TyOp ("U8", [])
(* let tBool = Type.TyOp ("Bool", []) *)
let tString = Type.TyOp ("String", [])
let tUnit = Type.TyOp ("<>", [])
let tTuple members = Type.TyOp ("Tuple", members)
let tVector child = Type.TyOp ("Vector", [child])
let tSet members = Type.TyOp ("Set", [members])
let tDict key value = Type.TyOp ("Dict", [key; value])
let tVar gensym_state = Type.TyVar (TypeVariable.create gensym_state)
