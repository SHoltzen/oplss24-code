(** TinyPPL Implementation *)

(** tinyppl pure expressions *)
type pure_e =
  | And of pure_e * pure_e
  | Or of pure_e * pure_e
  | Not of pure_e
  | Ident of string
  | Ite of pure_e * pure_e * pure_e
  | True
  | False

(** tinyppl probabilistic expressions *)
type expr =
  | Flip       of float
  | Bind       of string * expr * expr
  | Return     of pure_e

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
  | Flip(f) -> failwith "TODO"
  | Bind(x, e1, e2) ->failwith "TODO"
  | Return(p) ->failwith "TODO"

(* some small examples *)
let within_epsilon a b = Float.abs (a -. b) < 0.0001

let prog1 = Flip 0.5

let prog2 = Bind("x", Flip(0.5), Return(Ident("x")))

let prog3 = Bind("x", Flip(0.5),
                 Bind("y", Flip(0.3),
                     Bind("z", Flip(0.7),
                          Return(Ite(Ident("x"), Ident("y"), Ident("z"))))))

let () =
  assert (within_epsilon (prob prog1 StringMap.empty true) 0.5);
  assert (within_epsilon (prob prog2 StringMap.empty true) 0.5);
  assert (within_epsilon (prob prog3 StringMap.empty true) 0.5)
