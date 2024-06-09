open Core_grammar


(** capture-avoiding substitution e[x/v] *)
let rec subst e x (v: value) : expr = 
  match e with 
  | Ident(id) when id = x -> Value(v)
  | Bind(id, e1, e2) when id != x -> Bind(id, subst e1 x v, subst e2 x v)
  | Bind(_) | Ident(_) | Value(_) | Unif | Flip(_) -> e
  | Observe(e1, e2) -> Observe(subst e1 x v, subst e2 x v)
  | Ite(g, thn, els) -> Ite(subst g x v, subst thn x v, subst els x v)
  | Plus(e1, e2) -> Plus(subst e1 x v, subst e2 x v)
  | Mul(e1, e2) -> Mul(subst e1 x v, subst e2 x v)
  | Lt(e1, e2) -> Lt(subst e1 x v, subst e2 x v)
  | Or(e1, e2) -> Or(subst e1 x v, subst e2 x v)
  | And(e1, e2) -> And(subst e1 x v, subst e2 x v)
  | Not(e) -> Not(subst e x v)
  | Return(e) -> Return(subst e x v)

(** converts a value to a float or panics *)
let v_to_f v = 
  match v with 
  | Real(v) -> v 
  | _ -> failwith "unreachable"

(** converts a value to a Boolean or panics *)
let v_to_b v = 
  match v with 
  | Bool(v) -> v
  | _ -> failwith "unreachable"

(* true if a value is bot *)
let is_bot v = 
  match v with 
  | Bot -> true 
  | _ -> false

(** implement the weighted sampling semantics *)
let rec sample (e: Core_grammar.expr) : value = 
  match e with
  | Ident(x) -> failwith (Format.sprintf "attempting to sample %s" x)
  | Value(v) -> v
  | Plus(e1, e2) -> 
    let s1 = v_to_f (sample e1) and s2 = v_to_f (sample e2) in 
    Real(s1 +. s2)
  | Mul(e1, e2) -> 
    let s1 = v_to_f (sample e1) and s2 = v_to_f (sample e2) in 
    Real(s1 *. s2)
  | Lt(e1, e2) -> 
    let s1 = v_to_f (sample e1) and s2 = v_to_f (sample e2) in 
    Bool(s1 < s2)
  | Or(e1, e2) -> 
    let s1 = v_to_b (sample e1) and s2 = v_to_b (sample e2) in 
    Bool(s1 || s2)
  | And(e1, e2) -> 
    let s1 = v_to_b (sample e1) and s2 = v_to_b (sample e2) in 
    Bool(s1 && s2)
  | Not(e) -> 
    let s = v_to_b (sample e) in 
    Bool(not s)
  | Ite(g, thn, els) -> 
    let sg = v_to_b (sample g) in 
    if sg then sample thn else sample els
  | Bind(id, e1, e2) -> 
    let s1 = sample e1 in 
    if is_bot s1 then Bot else 
      let e2sub = subst e2 id s1 in
      sample e2sub
  | Observe(e1, e2) -> 
    (match sample e1 with 
     | Bot -> Bot 
     | Bool(v) -> if v then sample e2 else Bot
     | _ -> failwith "unreachable")
  | Unif -> Real(Util.sample_uniform 0.0 1.0)
  | Flip(theta) -> Bool(Util.sample_bool theta)
  | Return(e) -> sample e


(* implement the eval semantics: loop until you get an accepted sample *)
let rec eval e : value = 
  match sample e with 
  | Bot -> eval e 
  | v -> v



(** compute an importance estimate for the program with n samples*)
let estimate (p: Core_grammar.program) (n: int) =
  let e = ref 0.0 in
  for _ = 0 to n do
    let s = eval p.body in 
    if v_to_b s then e := !e +. 1.0;
  done;
  !e /. (float_of_int n)
