(* stateful actions in pure functions *)

(*

A procedure is a command to change the world.

Here it's power contained, it can only manipulate the small world given it.

Therefore, a proc is a function of `state -> (new_state, return_value)`, bound in a `result` type.

`andThen` will run one procedure with a given state, and a second procedure with the resulting state of the first one.

`doto` takes a `proc list` and a `state`, and `andThen`s them all.

`doto [ inc`
`					; inc`
`					; set 1335`
`					; inc`
`					; inc]  5;;` (* gives `Ok (1337, ())`. inc returns nothing, thus `()` *)

 Author: Martin Josefsson 2020AD

 *)

type ('state, 'return, 'error) proc =
  'state -> ('state * 'return, 'error) result

type example_state =
  int

let inc (state: 'state): ('state * 'return, 'error) result =
  (* First is the new state, second is the return value. *)
  Ok (state + 1, ())     (* inc returns nothing, thus `()`. *)

let dec (state: 'state): ('state * 'return, 'error) result =
  Ok (state - 1, ())

let andThen
      (proc0: ('state, 'return0, 'error0) proc)
      (proc1: ('state, 'return1, 'error1) proc)
      (state: 'state) =
  match proc0 state with           (* if proc0 succeeds *)
  | Ok (new_state, proc0_res) ->
     (match proc1 new_state with   (* AND proc1 succeeds *)
      | Ok (new_state, proc1_res) ->
         Ok (new_state, proc1_res) (* Give back the new state with result *)
      | Error e -> Error e)
  | Error e -> Error e

let update f state =
  Ok (f state, (), false)

let set v state =
  Ok (v, (), false)

let comp f g x = f (g x)

let noop (state: 'state): ('state, 'return, 'error) proc =
  function | _ -> Ok (state, ())

let return proc state = match proc state with
  | Ok (new_state, return, is_return) ->
     Ok (new_state, return, true)
  | Error e ->
     Error e

let rec doto (procs: (('state, 'return, 'error) proc) list) (state: 'state) =
  match procs with
  | proc :: [] ->
     proc state
  | proc :: other_actions ->
     andThen
       proc
       (doto other_actions)
       state
  | [] ->
     Error "Can't do no procs"
