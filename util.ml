let str = String.concat ""

let println strings =
  print_string(str strings);
  print_newline()

let rec luke_3_17               (* Separate the wheat from the chaff *)
          (list: (('a, 'err) result) list): ('a list, 'err list) result =
  let rec oks ress acc =
    match ress with
    | Ok x :: rest -> oks rest (x :: acc)
    | Error e :: rest -> oks rest acc
    | [] -> List.rev acc in
  let rec errors ress acc =
    match ress with
    | Ok x :: rest ->
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

let second = function (first, second) -> second

let comp f g x = f (g x)

let flip f x y = f y x

let equals x y = x = y

let neg f boolean = (not (f boolean))
