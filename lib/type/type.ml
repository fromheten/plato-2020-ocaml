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

   and TypeOperator: sig
     type t = string * Type.t list (* name, types. Think unification algorithm! *)
     val create: string -> Type.t list -> t
     val to_string: gensym_state -> t -> string
   end = struct
     type t = string * Type.t list
     let create n tl = (n, tl)
     let to_string gensym_state = function
         (name, types) ->
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

   and Type : sig
     type t = TyVar of TypeVariable.t
            | TyTag of (string * t)
            | TyTagUnion of (string * t) list
            | TyOp of TypeOperator.t
     val to_string: gensym_state -> t -> string
   end = struct
     type t = TyVar of TypeVariable.t
            | TyTag of (string * t)
            | TyTagUnion of (string * t) list
            | TyOp of TypeOperator.t
     let rec to_string gensym_state = function
       | TyVar tv -> TypeVariable.to_string gensym_state tv ^ "-" ^ string_of_int tv.id ^ tv.name
       | TyTag (tag, tagged_typ) ->
          "(" ^ tag ^ " " ^ to_string gensym_state tagged_typ ^ ")"
       | TyTagUnion cases ->
          "(union " ^ String.concat " " (List.map
                                           (to_string gensym_state)
                                           (List.map (fun x -> TyTag x) cases))
       | TyOp top -> TypeOperator.to_string gensym_state top
   end

   and Function: sig
     val create: Type.t -> Type.t -> Type.t
   end = struct
     let create from_type to_type =
       Type.TyOp ("->", [from_type; to_type])
   end
