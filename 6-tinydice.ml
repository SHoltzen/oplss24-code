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
  | Flip       of float
  | Bind       of string * expr * expr
  | Return     of pure_e

type bdd_ptr = int

(** tiny bdd *)
type bdd =
  True
  | False
  | Node of { topvar: int; low: bdd_ptr; high: bdd_ptr }

type bdd_table = {
  backing_table: bdd Array.t;
  next_free: int ref;
  num_vars: int ref;
  compute_table: (bdd, int) Hashtbl.t
}

let fresh_bdd_table () : bdd_table =
  let arr = Array.make 10000 True in
  Array.set arr 1 False;
  { backing_table=arr; next_free = ref 2; num_vars = ref 0; compute_table = Hashtbl.create 100 }


(* let get_or_insert (table:bdd_table) (bdd:bdd) : bdd_ptr = *)


let true_ptr = 0

let false_ptr = 1

(** get a fresh BDD variable *)
(* let fresh_var (tbl: bdd_table) : bdd_ptr = *)
(*   let fresh_var = !tbl.num_vars in *)
(*   tbl.num_vars := fresh_var + 1; *)
  


(** top-level symbol *)
type program = { body: expr }

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

let infer (e:expr) (v:bool) : float =
  prob e (StringMap.empty) v
