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
