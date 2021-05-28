(* If every item in the list is Some, return a Some list *)
let list_option_of_option_list opts =
  let rec inner acc opts = match opts with
    | Some x :: [] -> Some (List.rev (x :: acc))
    | Some x :: rest -> inner (x :: acc) rest
    | _ -> None in
  inner [] opts

let comp f g x = f (g x)

let is_ok res = match res with
  | Ok _ -> true
  | Error _ -> false

let is_error res = not (is_ok res)

let list_result_of_result_list ress =
  let rec inner ress oks errs =
    match ress with
    | Ok ok :: rest -> inner rest (ok :: oks) errs
    | Error e :: rest -> inner rest oks (e :: errs)
    | [] -> if errs = []
            then Ok (List.rev oks)
            else Error (List.rev errs) in
  inner ress [] []

let str = String.concat ""

let println strings =
  print_string (str strings);
  print_newline ()

let luke_3_17               (* Separate the wheat from the chaff *)
      (list: (('a, 'err) result) list): ('a list, 'err list) result =
  let rec oks ress acc =
    match ress with
    | Ok x :: rest -> oks rest (x :: acc)
    | Error _e :: rest -> oks rest acc
    | [] -> List.rev acc in
  let rec errors ress acc =
    match ress with
    | Ok _x :: rest ->
       errors rest acc
    | Error e :: rest ->
       errors rest (e :: acc)
    | [] ->
       List.rev acc in
  if List.length (errors list []) > 0
  then Ok (oks list [])
  else Error (errors list [])

let take_ok f = function
  | Ok x -> Ok (f x)
  | Error e -> Error e

let second = function (_first, second) -> second

let flip f x y = f y x

let equals x y = x = y

let neg f boolean = (not (f boolean))

let xyyx f x y = f y x

let do_then res then_fn =
  match res with
  | Ok value -> then_fn value
  | Error e -> Error e

let do_then_error x then_fn else_fn =
  match x with
  | Ok value -> then_fn value
  | Error e -> else_fn e

let app fn x =
    fn x
