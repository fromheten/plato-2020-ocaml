type state = { args: string list
             ; print_tests: bool
             }

let skip_one state = match state with
  | { args = first :: rest } -> Ok { state with args = rest }
  | _ -> Error "skip_one given empty args"

let print_tests state = match state with
  | { args = first :: rest } when first = "--test-results" ->
     Ok { state with print_tests = true }
  | _ -> Error "first one is not equal to --test-results"

let parse = State.and_then skip_one print_tests
