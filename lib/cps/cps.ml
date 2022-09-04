(* No-Brainer CPS Conversion, courtesy of Milo Davis, William Meehan, and Olin
   Shivers, Northeastern University, USA. Great work! *)
type var = string

let gensym =
  let counter = ref 0 in
  fun s ->
    counter := 1 + !counter;
    Printf.sprintf "%s_%d" s !counter


module StringMap = Map.Make (String)

(* syntax of CPS target language *)
type target_language =
  (* Function App *)
  | Call of triv * triv * cont
  (* Cont App *)
  | Ret of cont * triv
  (* Conditional *)
  | CIf of triv * target_language * target_language
  (* Cont binding *)
  | Letc of var * cont * target_language

and cont =
  | Cont of var * target_language
  | CVar of var
  | HALT

and triv =
  | Lam of var * var * target_language (* (lam (x k) p) *)
  | UVar of var

(* Abstract args *)
type abstract_arg =
  | AAVar of var (* A normal user variable *)
  | AAClosure of var * Expr.expr * env
(* A static closure *)

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
    (exp : Expr.expr)
    (env : abstract_arg StringMap.t)
    (c : abstract_continuation)
    (counts : int StringMap.t) : target_language * int StringMap.t =
  match exp with
  | Expr.Sym (_, y) -> ret c (StringMap.find y env) counts
  | Expr.Lam (_, [ (Expr.PSym (_, y), e) ]) ->
    ret c (AAClosure (y, e, env)) counts
  | App (_, e1, e2) -> cps e1 env (FCont (e2, env, c)) counts
  | IfThenElse (_, e1, e2, e3) -> cps e1 env (IfCont (e2, e3, env, c)) counts
  | _ -> failwith "CPS conversion not done for this expression type"


(* Three smart constructors, for RET, CALL, and IF forms *)
and ret
    (continuation : abstract_continuation)
    (arg : abstract_arg)
    (counts : int StringMap.t) : target_language * int StringMap.t =
  match continuation with
  | AHALT
  | KVar _ ->
    let cont, counts2 = bless_abstract_continuation continuation counts in
    let arg, counts3 = bless_abstract_arg arg counts2 in
    (Ret (cont, arg), counts3)
  | FCont (exp, env, c') -> cps exp env (ArgCont (arg, c')) counts
  | ArgCont (a', c') -> call a' arg c' counts
  | IfCont (e1, e2, env, c') -> cif arg e1 e2 c' env counts


and call
    (f : abstract_arg)
    (a : abstract_arg)
    (c : abstract_continuation)
    (counts : int StringMap.t) : target_language * int StringMap.t =
  match f with
  | AAVar _ ->
    let func, counts2 = bless_abstract_arg f counts in
    let arg, counts3 = bless_abstract_arg a counts2 in
    let cont, counts4 = bless_abstract_continuation c counts3 in
    (Call (func, arg, cont), counts4)
  | AAClosure (y, body, env) ->
    if one_ref y
    then cps body (extend y a env) c counts
    else
      let arg, counts2 = bless_abstract_arg a counts in
      ( match arg with
      | UVar x -> cps body (extend y (AAVar x) env) c counts2
      | Lam _ ->
        (* We've got a "let" redex, binding y to a lambda ter: ((FUN y body)
           (FUN ...)) We can't reduce this because y has multiple references in
           body, which would replicate the (FUN ...) term. So we produce a CPS
           "let", encoded as a CONT redex: (RET (CONT x body') (LAM ...)) where
           body' is body cps-converted with the original continuation c, and the
           (LAM ...) term is the cps-conversion of the (FUN ...) argument. *)
        let x = gensym "x" in
        let counts3 = new_count x counts2 in
        let env' = extend y (AAVar x) env in
        let b, counts4 = cps body env' c counts3 in
        (Ret (Cont (x, b), arg), counts4) )


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
    let condition, counts2 = bless_abstract_arg abstract_arg counts in
    let then_, counts3 = cps e1 env continuation counts2 in
    let else_, counts4 = cps e2 env continuation counts3 in
    (CIf (condition, then_, else_), counts4)
  | FCont _
  | ArgCont _
  | IfCont _ ->
    let jv = gensym "join" in
    let body, counts2 = cif abstract_arg e1 e2 (KVar jv) env counts in
    let join, counts3 = bless_abstract_continuation continuation counts2 in
    (Letc (jv, join, body), counts3)


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
    let counts2 = new_count x counts in
    let body, counts3 = ret c (AAVar x) counts2 in
    (Cont (x, body), counts3)


and bless_abstract_arg abstract_arg counts =
  match abstract_arg with
  | AAVar x -> (UVar x, incr x counts)
  | AAClosure (y, body, env) ->
    let x = gensym y in
    let k = gensym "k" in
    let env' = extend y (AAVar x) env in
    let b, counts' = cps body env' (KVar k) (new_count x counts) in
    (* The eta-reduction check. Note that we don't have to check reference
       counts on k, as continuation variables are linear. *)
    ( match b with
    | Call (f, UVar x', CVar k') ->
      if x = x' && k = k' && StringMap.find x counts' = 1
      then (f, counts')
      else (Lam (x, k, b), counts')
    | _ -> (Lam (x, k, b), counts') )


let cps_tests = []
