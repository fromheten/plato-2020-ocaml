(* Simple implementation of URI safe base64 after Simon Josefsson *)
(* Copyright Martin Josefsson (no relation) - licence = public domain *)

let char_list string =
  let rec exp i l =
    if i < 0
    then l
    else exp (i - 1) (string.[i] :: l)
  in exp (String.length string - 1) []

let b64_alphabet = char_list "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/"

(* function mapping encoded char to decoded char *)
(* TODO make me a table, this is inefficient *)
let char_from_b64char_opt b64char: int option =
  let rec inner b64char alphabet index =
    match alphabet with
    | head :: alphabet_tail ->
       if head = b64char
       then Some index
       else inner b64char alphabet_tail (index + 1)
    | [] -> None in
  inner b64char b64_alphabet 0

let char_from_b64char b64char =
  match char_from_b64char_opt b64char with
  | Some n -> n
  | None -> 0

let unwrap opt msg = match opt with
  | Some x -> x
  | None -> failwith msg

let default opt default_val = match opt with
  | Some x -> x
  | None -> default_val

let encodeblock (input: char list) (len: int) =
  (unwrap
     (List.nth_opt b64_alphabet
        ((land)
           ((lsr)
              (Char.code (unwrap
                            (List.nth_opt input 0)
                            "position 1"))
              2)
           0x3f))
     "pos 1")
  :: (unwrap
        (List.nth_opt b64_alphabet
           ((land)
              ((+)
                 ((Char.code (unwrap
                                (List.nth_opt input 0)
                                "2.1"))
                  lsl 4)
                 ((Char.code (default
                                (List.nth_opt input 1)
                                '\x00'))
                  lsr 4))
              0x3f))
        "aaa")
  :: (if len > 1
      then (unwrap
              (List.nth_opt b64_alphabet
                 ((land)
                    ((+)
                       ((Char.code (unwrap
                                      (List.nth_opt input 1)
                                      "2.1"))
                        lsl 2)
                       ((Char.code (default
                                      (List.nth_opt input 2)
                                      '\x00'))
                        lsr 6))
                    0x3f))
              "position 3")
      else '=')
  :: (if len > 2
      then (List.nth b64_alphabet ((Char.code (List.nth input 2)) land 0x3f))
      else '=')
  :: []

let string_of_char_list char_list =
  String.concat "" (List.map (String.make 1) char_list)

let rec b64_encode (input: char list) acc =
  match input with
  | _c0 :: _c1 :: _c2 :: rest ->
     b64_encode rest (List.append acc (encodeblock input 3))
  | _c0 :: _c1 :: [] ->
     b64_encode [] (List.append acc (encodeblock input 2))
  | _c0 :: [] ->
     b64_encode [] (List.append acc (encodeblock input 1))
  | [] ->
     acc

let isbase64 chr = List.mem chr b64_alphabet

let chr_opt n =
  print_int n; print_newline ();
  try Some (Char.chr n) (* 0xff = 11111111 = 255 *)
  with | Invalid_argument _a -> None

let decodeblock4 c0 c1 c2 c3: char list =
  if isbase64 c0 && isbase64 c1
  then let c0_code_lsl = ((char_from_b64char c0) lsl 2) in (* throw away the leftmost bits - they are always 00 *)
       let c1_code_lsr = (char_from_b64char c1) lsr 4 in (* 00111111 -> 00000011 *)
       let output_byte_0 = (lor) c0_code_lsl c1_code_lsr in
       if c2 = '=' && c3 = '='   (* The reference implementation is wrong! We disagree and claim sovereignety (also regarding spelling) *)
       then [Char.chr output_byte_0]
       else if isbase64 c2
       then let c1_code_lsl = ((char_from_b64char c1) lsl 4) land 0xf0 in (* 00111111 -> 11110000 *)
            let c2_code_lsr = (char_from_b64char c2) lsr 2 in
            let output_byte_1 = (lor) c1_code_lsl c2_code_lsr in
            if c3 = '='
            then [unwrap (chr_opt output_byte_0) "Fail 2"; unwrap (chr_opt output_byte_1) "Fail 3"]
            else if isbase64 c3
            then let c2_code_lsl = ((char_from_b64char c2) lsl 6) land 0xc0 in (* 00111111 -> 11000000 *)
                 let c3_code_lsr = (char_from_b64char c3) in
                 let output_byte_2 = (lor) c2_code_lsl c3_code_lsr in
                 [unwrap (chr_opt output_byte_0) "Fail 4"
                 ;unwrap (chr_opt output_byte_1) "Fail 5"
                 ;unwrap (chr_opt output_byte_2) "Fail 6"]
            else failwith "c3 be wild yo bro"
       else failwith "c2 be outta this wooooorld"
  else failwith "give me the right stuff you vile human!!!!"

let rec b64_decode (input: char list) acc =
  match input with
  | c0 :: c1 :: c2 :: c3 :: rest ->
     b64_decode rest (List.append acc (decodeblock4 c0 c1 c2 c3))
  | [] ->
     Ok acc
  | _ ->
     Error "A Base64-string must contain 4 characters - the smallest string is `AA==`"
