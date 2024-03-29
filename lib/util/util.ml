(* If every item in the list is Some, return a Some list *)
let list_option_of_option_list opts =
  let rec inner acc opts =
    match opts with
    | [ Some x ] -> Some (List.rev (x :: acc))
    | Some x :: rest -> inner (x :: acc) rest
    | _ -> None
  in
  inner [] opts


let comp f g x = f (g x)

let is_ok res =
  match res with
  | Ok _ -> true
  | Error _ -> false


let is_error res = not (is_ok res)

let list_result_of_result_list ress =
  let rec inner ress oks errs =
    match ress with
    | Ok ok :: rest -> inner rest (ok :: oks) errs
    | Error e :: rest -> inner rest oks (e :: errs)
    | [] -> if errs = [] then Ok (List.rev oks) else Error (List.rev errs)
  in
  inner ress [] []


let str = String.concat ""

let char_list s =
  let rec exp i l = if i < 0 then l else exp (i - 1) (s.[i] :: l) in
  exp (String.length s - 1) []


let string_of_char_list char_list = str (List.map (String.make 1) char_list)

let println strings =
  print_string (str strings);
  print_newline ()


let luke_3_17 (* Separate the wheat from the chaff *)
    (list : ('a, 'err) result list) : ('a list, 'err list) result =
  let rec oks ress acc =
    match ress with
    | Ok x :: rest -> oks rest (x :: acc)
    | Error _e :: rest -> oks rest acc
    | [] -> List.rev acc
  in
  let rec errors ress acc =
    match ress with
    | Ok _x :: rest -> errors rest acc
    | Error e :: rest -> errors rest (e :: acc)
    | [] -> List.rev acc
  in
  if List.length (errors list []) > 0
  then Ok (oks list [])
  else Error (errors list [])


let take_ok f = function
  | Ok x -> Ok (f x)
  | Error e -> Error e


let second = function
  | _first, second -> second


let flip f x y = f y x

let equals x y = x = y

let neg f boolean = not (f boolean)

let xyyx f x y = f y x

let do_then res then_fn =
  match res with
  | Ok value -> then_fn value
  | Error e -> Error e


let do_then_error x then_fn else_fn =
  match x with
  | Ok value -> then_fn value
  | Error e -> else_fn e


let app fn x = fn x

let all_ok results =
  let rec inner acc rest =
    match rest with
    | Ok value :: rest -> inner (value :: acc) rest
    | Error e :: _rest -> Error e
    | [] -> Ok acc
  in
  inner [] results


let all_some options =
  let rec inner acc rest =
    match rest with
    | Some value :: rest -> inner (value :: acc) rest
    | None :: _rest -> None
    | [] -> Some acc
  in
  inner [] options


let all_oks results =
  let rec inner results vals errs =
    match results with
    | Ok x :: rest -> inner rest (x :: vals) errs
    | Error e :: rest -> inner rest vals (e :: errs)
    | [] -> if List.length errs = 0 then Ok vals else Error errs
  in
  inner results [] []


let string_of_in_channel (ch : in_channel) : string =
  let rec inner acc =
    try
      let letter = really_input_string ch 1 in
      inner (acc ^ letter)
    with
    | End_of_file -> acc
  in
  inner ""


let puts s =
  print_string s;
  print_newline ()


let string_of_pos pos =
  match pos with
  | start, finish ->
    Printf.sprintf "(pos %s, %s)" (string_of_int start) (string_of_int finish)


let unwrap res to_string =
  match res with
  | Ok x -> x
  | Error e -> failwith (to_string e)


let rec fill_string (filling : string) (count : int) (acc : string) =
  if count > 0 then fill_string filling (count - 1) (acc ^ filling) else acc


let debugprint_format label examples =
  let debugprint_inner indent_count examples =
    let table_contents =
      List.map (fun (label, text) -> label ^ ":\n" ^ text) examples
    in
    let formatted_table_contents =
      List.map
        (fun row -> fill_string "  " indent_count "" ^ row)
        table_contents
    in
    String.concat "\n" formatted_table_contents
  in
  let label_underline = fill_string "#" (String.length label) "" in
  "\n"
  ^ label
  ^ "\n"
  ^ label_underline
  ^ "\n"
  ^ debugprint_inner 0 examples
  ^ "\n"
  ^ label_underline
  ^ "\n"


let debugprint label = comp print_string (debugprint_format label)

let pascal_case string =
  let first_char = String.get string 0 in
  first_char = Char.uppercase_ascii first_char


let read_whole_file (filename : string) : string =
  let ch = open_in filename in
  let s = really_input_string ch (in_channel_length ch) in
  close_in ch;
  s
