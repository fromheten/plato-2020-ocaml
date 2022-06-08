(* Recreating state in pure function works by making a pure function of the old state, some data, returning the new state, and the transformed data.
 * takes a function f, an initial state, and a list of arguments
 * Applies f initial_state first_arg
 * This returns a new state and a result
 * The result is concatenated onto a grand result
 * The new state is used to the second argument, et cetera *)

let rec map f acc state = function
  | x :: xs ->
    let state, result = f state x in
    map f (List.cons result acc) state xs
  | [] -> (state, List.rev acc)


let rec exists f state = function
  | [] -> (state, false)
  | x :: xs ->
    let state, (result : bool) = f state x in
    if result then (state, result) else exists f state xs


let unwrap string_of_err = function
  | Ok value -> value
  | Error e ->
    let (e : string) = string_of_err e in
    failwith e
