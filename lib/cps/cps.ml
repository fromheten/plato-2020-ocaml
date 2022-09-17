(* No-Brainer CPS Conversion, courtesy of Milo Davis, William Meehan, and Olin
   Shivers, Northeastern University, USA. Great work! *)
type var = string [@@deriving show]

let gensym =
  let counter = ref 0 in
  fun s ->
    counter := 1 + !counter;
    Printf.sprintf "%s_%d" s !counter


module StringMap = Map.Make (String)
[@@deriving show]

(* syntax of CPS target language *)
type target_language =
  (* Function App *)
  | LamApp of triv * triv * cont
  (* Cont App *)
  | ContApp of cont * triv
  (* Conditional *)
  | CIf of triv * target_language * target_language
  (* Cont binding *)
  | Letc of var * cont * target_language
[@@deriving show]
and cont =
  | Cont of var * target_language
  | CVar of var
  | HALT

and triv =
  | Lam of var * var * target_language (* (lam (x k) p) *)
  | UVar of var
  | UString of string
  | UBool of bool
  | UU8 of int
[@@deriving show]

(* Abstract args *)
type abstract_arg =
  | AAVar of var (* A normal user variable *)
  | AAClosure of var * Expr.expr * env (* A static closure *)
  | ACString of string
  | ACBool of bool
  | ACU8 of int

and env = abstract_arg StringMap.t

(* Abstract continuations *)
type abstract_continuation =
  | AHALT
  | KVar of var
  | FCont of Expr.expr * env * abstract_continuation
  | ArgCont of abstract_arg * abstract_continuation
  | IfCont of Expr.expr * Expr.expr * env * abstract_continuation

(* We assume singly-referenced vars are marked with a ":" prefix *)
let one_ref y = String.length y >= 1 && String.sub y 0 1 = ":"

(* Extend a static environment with a new [y |-> a] entry *)
let extend y a env = StringMap.add y a env

(* Utilities to maintain reference counts of user vars in CPS term *)
let new_count x counts = StringMap.add x 0 counts

let incr x counts = StringMap.add x (1 + StringMap.find x counts) counts

(* The top-level function *)
let rec cps
    (expr : Expr.expr)
    (env : abstract_arg StringMap.t)
    (abstract_continuation : abstract_continuation)
    (counts : int StringMap.t) : target_language * int StringMap.t =
  match expr with
  | Expr.Sym (_, s) ->
    cont_app abstract_continuation (StringMap.find s env) counts
  | Expr.Lam (_, (Expr.PSym (_, arg_name), e) :: _rest) ->
    cont_app abstract_continuation (AAClosure (arg_name, e, env)) counts
  | Lam (_, (PTag (_, _, _), _)::_) ->
    failwith "CPS conversion not done for tag lambdas type"
  | Lam (_, []) -> failwith "can't cps empty lambda"
  | App (_, e1, e2) ->
    cps e1 env (FCont (e2, env, abstract_continuation)) counts
  | IfThenElse (_, e1, e2, e3) ->
    cps e1 env (IfCont (e2, e3, env, abstract_continuation)) counts
  | String (_, s) ->
    cont_app abstract_continuation (ACString s) counts
  | Bool (_, b) ->
    cont_app abstract_continuation (ACBool b) counts
  | U8 (_, u8) ->
    cont_app abstract_continuation (ACU8 u8) counts
  | Ann (_pos, _t, e) ->
    cps e env abstract_continuation counts
  | Tuple (_, _) ->
    failwith (Printf.sprintf "CPS conversion not done for %s" (Expr.string_of_expr expr))
  | Unit _ ->
    failwith (Printf.sprintf "CPS conversion not done for %s" (Expr.string_of_expr expr))
  | Vector (_, _) ->
    failwith (Printf.sprintf "CPS conversion not done for %s" (Expr.string_of_expr expr))

  | Set (_, _) ->
    failwith (Printf.sprintf "CPS conversion not done for %s" (Expr.string_of_expr expr))
  | Dict (_, _) ->
    failwith (Printf.sprintf "CPS conversion not done for %s" (Expr.string_of_expr expr))
  | Let (_, _, _, _) ->
    failwith (Printf.sprintf "CPS conversion not done for %s" (Expr.string_of_expr expr))
  | (Builtin _) ->
    failwith (Printf.sprintf "CPS conversion not done for this expression %s" (Expr.string_of_expr expr))

(* Three smart constructors, for ContApp, LamApp, and IF forms *)
and cont_app
    (continuation : abstract_continuation)
    (arg : abstract_arg)
    (counts : int StringMap.t) : target_language * int StringMap.t =
  match continuation with
  | AHALT
  | KVar _ ->
    let cont, counts2 = bless_abstract_continuation continuation counts in
    let arg, counts3 = bless_abstract_arg arg counts2 in
    (ContApp (cont, arg), counts3)
  | FCont (exp, env, c') -> cps exp env (ArgCont (arg, c')) counts
  | ArgCont (inner_arg, inner_continuation) ->
    lam_app inner_arg arg inner_continuation counts
  | IfCont (e1, e2, env, continuation) ->
    cif arg e1 e2 continuation env counts


and lam_app
    (fn : abstract_arg)
    (arg : abstract_arg)
    (continuation : abstract_continuation)
    (counts : int StringMap.t) : target_language * int StringMap.t =
  match fn with
  | AAVar _ ->
    let fn, counts = bless_abstract_arg fn counts in
    let arg, counts = bless_abstract_arg arg counts in
    let continuation, counts = bless_abstract_continuation continuation counts in
    (LamApp (fn, arg, continuation), counts)
  | AAClosure (closure_arg, body, env) ->
    if one_ref closure_arg
    then cps body (extend closure_arg arg env) continuation counts
    else
      let arg, counts = bless_abstract_arg arg counts in
      ( match arg with
        | UVar uvar ->
          cps body (extend closure_arg (AAVar uvar) env) continuation counts
        | UString s ->
          cps body (extend closure_arg (ACString s) env) continuation counts
        | UBool b ->
          cps body (extend closure_arg (ACBool b) env) continuation counts
        | UU8 u8 ->
          cps body (extend closure_arg (ACU8 u8) env) continuation counts
        | Lam _ ->
          (* We've got a "let" redex, binding y to a lambda ter: ((FUN y body)
             (FUN ...)) We can't reduce this because y has multiple references in
             body, which would replicate the (FUN ...) term. So we produce a CPS
             "let", encoded as a CONT redex: (RET (CONT x body') (LAM ...)) where
             body' is body cps-converted with the original continuation c, and the
             (LAM ...) term is the cps-conversion of the (FUN ...) argument. *)
          let x = gensym "x" in
          let counts = new_count x counts in
          let env = extend closure_arg (AAVar x) env in
          let b, counts = cps body env continuation counts in
          (ContApp (Cont (x, b), arg), counts) )
  | ACString s ->
    failwith (Printf.sprintf "Can't CPS convert a function where f is a String. f: %s" s)
  | ACBool b ->
    failwith (Printf.sprintf "Can't CPS convert a function where f is a Bool. f: %s" (string_of_bool b))
  | ACU8 b ->
    failwith (Printf.sprintf "Can't CPS convert a function where f is a U8. f: %s" (string_of_int b))


and cif
    (abstract_arg : abstract_arg)
    (e1 : Expr.expr)
    (e2 : Expr.expr)
    (continuation : abstract_continuation)
    (env : abstract_arg StringMap.t)
    (counts : int StringMap.t) =
  match continuation with
  | AHALT
  | KVar _ ->
    let condition, counts = bless_abstract_arg abstract_arg counts in
    let then_, counts = cps e1 env continuation counts in
    let else_, counts = cps e2 env continuation counts in
    (CIf (condition, then_, else_), counts)
  | FCont _
  | ArgCont _
  | IfCont _ ->
    let jv = gensym "join" in
    let body, counts = cif abstract_arg e1 e2 (KVar jv) env counts in
    let join, counts = bless_abstract_continuation continuation counts in
    (Letc (jv, join, body), counts)


(* Two "blessing functions to render abstract continuations and abstract
   arguments into actual syntax" *)
and bless_abstract_continuation
    (c : abstract_continuation) (counts : int StringMap.t) :
    cont * int StringMap.t =
  match c with
  | AHALT -> (HALT, counts)
  | KVar kv -> (CVar kv, counts)
  | FCont _
  | ArgCont _
  | IfCont _ ->
    let x = gensym "x" in
    let counts = new_count x counts in
    let body, counts = cont_app c (AAVar x) counts in
    (Cont (x, body), counts)


and bless_abstract_arg abstract_arg counts =
  match abstract_arg with
  | AAVar x -> (UVar x, incr x counts)
  | AAClosure (arg_name, body, env) ->
    let arg_symbol = gensym arg_name in
    let continuation = gensym "k" in
    let env = extend arg_name (AAVar arg_symbol) env in
    let body_cps, counts = cps body env (KVar continuation) (new_count arg_symbol counts) in
    (* The eta-reduction check. Note that we don't have to check reference
       counts on k, as continuation variables are linear. *)
    ( match body_cps with
    | LamApp (fn, UVar bodyfn_arg_symbol, CVar bodyfn_continuation) ->
      if arg_symbol = bodyfn_arg_symbol
      && continuation = bodyfn_continuation
      && StringMap.find arg_symbol counts = 1
      then (fn, counts)
      else (Lam (arg_symbol, continuation, body_cps), counts)
    | _ -> (Lam (arg_symbol, continuation, body_cps), counts) )
  | ACString s -> (UString s, counts)
  | ACBool b -> (UBool b, counts)
  | ACU8 u8 -> (UU8 u8, counts)

let cps_easy expr = cps expr StringMap.empty AHALT StringMap.empty

let cps_tests = [
  "Cps works",
  cps_easy
    (Read.parse_dangerously "(((λ x (λ y x)) \"first\") \"second\")")
  = ((ContApp (HALT, (UString "first"))), StringMap.empty)
]
