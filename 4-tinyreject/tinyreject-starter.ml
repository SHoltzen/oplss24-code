(** tinydisc language *)
type pure_e =
  | And of pure_e * pure_e
  | Or of pure_e * pure_e
  | Not of pure_e
  | Ident of string
  | Ite of pure_e * pure_e * pure_e
  | True
  | False

(** core grammar type *)
type expr =
  | Flip of float
  | Bind of string * expr * expr
  | Return of pure_e
  | Observe of pure_e * expr

module StringMap = Map.Make(String)

type env = bool StringMap.t

exception Runtime

let rec pure_eval (e:pure_e) (env:env) : bool =
  match e with
  | True -> true
  | False -> false
  | Not(e) -> not (pure_eval e env)
  | And(e1, e2) ->
    (pure_eval e1 env) && (pure_eval e2 env)
  | Or(e1, e2) ->
    (pure_eval e1 env) || (pure_eval e2 env)
  | Ite(g, thn, els) ->
    if (pure_eval g env) then (pure_eval thn env) else (pure_eval els env)
  | Ident(x) ->
    (match StringMap.find_opt x env with
     | Some(v) -> v
     | None -> raise Runtime)

(** given an expression `e` and environment `env`, draw a sample from `e` *)
let rec sample (e:expr) (env:env) : bool option =
  match e with
  | Flip(f) -> if (Random.float 1.0) < f then Some(true) else Some(false)
  | Bind(x, e1, e2) ->
    (match sample e1 env with
     | Some(v1) ->
       let new_env = StringMap.add x v1 env in
       sample e2 new_env
     | None -> None)
  | Observe(e1, e2) ->
    failwith "TODO"
  | Return(p) -> Some(pure_eval p env)

(* use the expectation estimator to estimate the probability that `e` evaluates
   to `v` using `num_samples` *)
let estimate (e:expr) (v:bool) (num_samples: int) : float =
  failwith "TODO"


let ex_prog = Bind("x", Flip(0.3),
                  Bind("y", Flip(0.4),
                      Return(And(Ident("x"), Ident("y")))))

(* some example runs:
   > estimate (Flip 0.4) true 1000;;
   - : float = 0.381
   estimate ex_prog true 100;;
   - : float = 0.13
*)

(* some small examples *)
let within_epsilon a b = Float.abs (a -. b) < 0.01

let prog1 = Flip 0.5

let prog2 = Bind("x", Flip(0.5), Return(Ident("x")))

let prog3 = Bind("x", Flip(0.5),
                 Bind("y", Flip(0.3),
                      Bind("z", Flip(0.7),
                           Return(Ite(Ident("x"), Ident("y"), Ident("z"))))))

let prog4 = Bind("x", Flip(0.5),
                 Bind("y", Flip(0.5),
                      Observe(Or(Ident("x"), Ident("y")),
                              Return(Ident("x")))))

let () =
  (* these assertions will fail (with small probability)! *)
  assert (within_epsilon (estimate prog1 true 10000) 0.5);
  assert (within_epsilon (estimate prog2 true 10000) 0.5);
  assert (within_epsilon (estimate prog3 true 10000) 0.5);
  assert (within_epsilon (estimate prog4 true 100000) 0.666666)

