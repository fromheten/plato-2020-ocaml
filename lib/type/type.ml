type gensym_state =
  { mutable next_variable_id : int
  ; mutable next_variable_name : char
  }

let new_gensym_state () = { next_variable_id = 0; next_variable_name = 'a' }

module rec TypeVariable : sig
  type t =
    { id : int
    ; mutable name : string
    ; mutable instance : Type.typ option
    }

  val create : gensym_state -> t

  val name : gensym_state -> t -> string

  val to_string : gensym_state -> t -> string

  val compare : t -> t -> int

  val hash : t -> int

  val equal : t -> t -> bool
end = struct
  type t =
    { id : int
    ; mutable name : string
    ; mutable instance : Type.typ option
    }

  let create gensym_state =
    gensym_state.next_variable_id <- gensym_state.next_variable_id + 1;
    { id = gensym_state.next_variable_id - 1; name = ""; instance = None }


  let name gensym_state tv =
    if tv.name = ""
    then (
      tv.name <- Char.escaped gensym_state.next_variable_name;
      gensym_state.next_variable_name <-
        Char.chr (Char.code gensym_state.next_variable_name + 1) );
    tv.name


  let to_string gensym_state tv =
    match tv.instance with
    | None -> name gensym_state tv
    | Some typ -> Type.to_string gensym_state typ


  let compare t1 t2 = t2.id - t1.id

  let hash tv = tv.id

  let equal tv1 tv2 = tv1.id = tv2.id
end

and Type : sig
  type pos = int * int

  type typ =
    | TyVar of pos * TypeVariable.t
    | TyTag of pos * string * typ
    | TyTagUnion of pos * (string * typ) list
    | TyOp of pos * string * typ list
    (* name, types. Think unification algorithm! *)
    | TyForall of pos * string * typ
    (* (Λ A (Λ B (: (-> A B B) (λ [x y] y)))) *)
    | TyApp of pos * typ * typ

  val to_string : gensym_state -> typ -> string
end = struct
  type pos = int * int

  type typ =
    | TyVar of pos * TypeVariable.t
    | TyTag of pos * string * typ
    | TyTagUnion of pos * (string * typ) list
    | TyOp of pos * string * typ list
    (* name, types. Think unification algorithm! *)
    | TyForall of pos * string * typ
    (* (Λ A (Λ B (: (-> A B B) (λ [x y] y)))) *)
    | TyApp of pos * typ * typ

  let rec to_string gensym_state = function
    | TyVar (_pos, tv) ->
      TypeVariable.to_string gensym_state tv
      ^ "-"
      ^ string_of_int tv.id
      ^ tv.name
    | TyTag (_pos, tag, tagged_typ) ->
      "(" ^ tag ^ " " ^ to_string gensym_state tagged_typ ^ ")"
    | TyTagUnion (_pos, cases) ->
      "(Union "
      ^ String.concat
          " "
          (List.map
             (to_string gensym_state)
             (List.map (fun (tag, value) -> TyTag (_pos, tag, value)) cases) )
      ^ ")"
    | TyOp (_pos, name, types) ->
      ( match types with
      | [] -> name
      | [ hd; tl ] ->
        Printf.sprintf
          "(%s %s %s)"
          name
          (Type.to_string gensym_state hd)
          (Type.to_string gensym_state tl)
      | _ ->
        types
        |> List.map (Type.to_string gensym_state)
        |> List.fold_left (fun a b -> a ^ " " ^ b) ""
        |> Printf.sprintf "%s %s" name )
    | TyForall (_pos, name, typ) ->
      Printf.sprintf "(Λ %s %s)" name (to_string gensym_state typ)
    | TyApp (_pos, f, x) ->
      Printf.sprintf
        "(TyApp %s %s)"
        (to_string gensym_state f)
        (to_string gensym_state x)
end

let negpos = (-1, -1)

let tArrow from_type to_type = Type.TyOp (negpos, "->", [ from_type; to_type ])

let tU8 = Type.TyOp (negpos, "U8", [])

(* let tBool = Type.TyOp ("Bool", []) *)
let tString = Type.TyOp (negpos, "String", [])

let tUnit = Type.TyOp (negpos, "<>", [])

let tTuple members = Type.TyOp (negpos, "Tuple", members) (* <x y z> *)

let tVector child = Type.TyOp (negpos, "Vector", [ child ])

let tSet members = Type.TyOp (negpos, "Set", [ members ])

let tDict key value = Type.TyOp (negpos, "Dict", [ key; value ])

let tVar gensym_state = Type.TyVar (negpos, TypeVariable.create gensym_state)

let type_tests = []
