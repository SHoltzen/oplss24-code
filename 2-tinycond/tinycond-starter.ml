(** pure language *)
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
  | Flip       of float
  | Bind       of string * expr * expr
  | Return     of pure_e
  | Observe    of pure_e * expr

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

(** given an expression `e` and environment `env`, compute the probability
    that `e` evaluates to `v` *)
let rec prob (e:expr) (env:env) (v:bool) : float =
  match e with
  | Flip(f) -> if v then f else (1.0 -. f)
  | Bind(x, e1, e2) ->
    let true_env = StringMap.add x true env in
    let false_env = StringMap.add x false env in
    let prob_e1_t = prob e1 env true in
    let prob_e1_f = prob e1 env false in
    (prob_e1_t *. (prob e2 true_env v)) +. (prob_e1_f *. (prob e2 false_env v))
  | Return(p) ->
    if (pure_eval p env) = v then 1.0 else 0.0
  | Observe(p, e) ->
    failwith "TODO"

let infer (e:expr) (v:bool) : float = failwith "TODO"

(* some small examples *)
let within_epsilon a b = Float.abs (a -. b) < 0.0001

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
  assert (within_epsilon (infer prog1 true) 0.5);
  assert (within_epsilon (infer prog2 true) 0.5);
  assert (within_epsilon (infer prog3 true) 0.5);
  assert (within_epsilon (infer prog4 true) 0.666666)
