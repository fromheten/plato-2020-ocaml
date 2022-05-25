type gensym_state =
  { mutable next_variable_id : int
  ; mutable next_variable_name : char
  }
[@@deriving yojson]

type gensym_info = int * char (* next_variable_id, next_variable_name *)

let string_of_info (next_variable_id, next_variable_name) =
  string_of_int next_variable_id ^ " " ^ String.make 1 next_variable_name


let info_of_state state = (state.next_variable_id, state.next_variable_name)

let state_of_info info =
  { next_variable_id = fst info; next_variable_name = snd info }


let setstate state info =
  state.next_variable_id <- fst info;
  state.next_variable_name <- snd info


let json_of_gensym_state : gensym_state -> string =
  Util.comp Yojson.Safe.to_string gensym_state_to_yojson


let new_gensym_state () = { next_variable_id = 0; next_variable_name = 'a' }

let inc_gensym_state gensym_state =
  let new_state =
    { next_variable_id = gensym_state.next_variable_id + 1
    ; next_variable_name =
        Char.chr (gensym_state.next_variable_id + 1 + Char.code 'a')
    }
  in
  new_state


module rec TypeVariable : sig
  type t =
    { id : int
    ; mutable name : string
    ; mutable instance : Type.typ option
    }

  val create : gensym_state -> t

  val name : gensym_state -> t -> string

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

  type t = typ

  val compare : t -> t -> int
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

  type t = typ

  let compare t0 t1 = if t0 = t1 then 1 else 0
end

let name_pure (state : gensym_info) (tv_name : string) : gensym_info * string =
  let next_variable_name = snd state in
  if tv_name = ""
  then
    let new_tv_name = Char.escaped next_variable_name in
    let new_next_variable_name = Char.chr (Char.code next_variable_name + 1) in
    ((fst state, new_next_variable_name), new_tv_name)
  else (state, tv_name)


let get_name (tv : TypeVariable.t) = tv.name

let typ_variable state name instance : gensym_info * TypeVariable.t =
  ((fst state + 1, snd state), { id = fst state; name; instance })


let rec string_of_typ_variable
    (state : gensym_info) (tv_instance : Type.typ option) (tv_name : string) :
    gensym_info * string =
  match tv_instance with
  | Some typ -> string_of_typ state typ
  | None -> name_pure state tv_name


and string_of_typ (state : gensym_info) : Type.typ -> gensym_info * string =
  function
  | TyVar (_pos, tv) ->
    let state, result = string_of_typ_variable state tv.instance tv.name in
    (state, result ^ "#-" ^ string_of_int tv.id ^ tv.name)
  | TyTag (_pos, tag, tagged_typ) ->
    let state, result = string_of_typ state tagged_typ in
    (state, "(" ^ tag ^ " " ^ result ^ ")")
  | TyTagUnion (_pos, _cases) -> failwith "Have to implement stateful map first"
  (* "(Union " * ^ String.concat * " " * (List.map * (string_of_typ
     next_variable_name) * (List.map (fun (tag, value) -> Type.TyTag (_pos, tag,
     value)) cases) ) * ^ ")" *)
  | TyOp (_pos, name, types) ->
    ( match types with
    | [] -> (state, name)
    | [ hd; tl ] ->
      let state, head = string_of_typ state hd in
      let state, tail = string_of_typ state tl in
      (state, Printf.sprintf "(%s %s %s)" name head tail)
    | _ ->
      failwith "have to implement stateful map first"
      (* types * |> List.map (string_of_typ next_variable_name) * |>
         List.fold_left (fun a b -> a ^ " " ^ b) "" * |> Printf.sprintf "%s %s"
         name *) )
  | TyForall (_pos, name, typ) ->
    let state, typ_name = string_of_typ state typ in
    (state, Printf.sprintf "(Λ %s %s)" name typ_name)
  | TyApp (_pos, f, x) ->
    let state, f_string = string_of_typ state f in
    let state, x_string = string_of_typ state x in
    (state, Printf.sprintf "(TyApp %s %s)" f_string x_string)


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

let tVar gensym_state : Type.typ =
  Type.TyVar (negpos, TypeVariable.create gensym_state)


let tVar_pure state =
  let state, tvar = typ_variable state "" None in
  (state, Type.TyVar (negpos, tvar))


let type_tests =
  [ (let expected = { next_variable_id = 2; next_variable_name = 'c' } in
     let actual = inc_gensym_state (inc_gensym_state (new_gensym_state ())) in
     ("inc_gensym_state incs", expected = actual) )
  ]
