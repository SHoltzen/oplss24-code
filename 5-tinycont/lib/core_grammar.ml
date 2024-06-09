(** Contains the internal core grammar for the discrete language *)
open Core

type value = 
  Real of float 
  | Bool of bool
  | Bot
[@@deriving sexp_of]

(** core grammar type *)
type expr =
  | Ident of string
  | Value of value
  | Observe of expr * expr
  | Bind of string * expr * expr
  | Ite of expr * expr * expr
  | Unif 
  | Flip of float
  | Plus of expr * expr 
  | Mul of expr * expr
  | Lt of expr * expr  (* less-than *)
  | Or of expr * expr 
  | And of expr * expr 
  | Not of expr
  | Return of expr
[@@deriving sexp_of]


(** top-level symbol *)
type program = { body: expr }
[@@deriving sexp_of]

exception Type_error of string

(** convert an expression in the external grammar into one in the internal grammar *)
let rec from_external_expr (e: Syntax.eexpr) =
  let f = from_external_expr in
  match e with
  | Ident(_, x) -> Ident(x)
  | Real(_, r) -> Value(Real(Bignum.to_float r))
  | Bool(_, v) -> Value(Bool(v))
  | Observe(_, e1, e2) -> Observe(f e1, f e2)
  | Bind(_, id, e1, e2) -> Bind(id, f e1, f e2)
  | Ite(_, g, thn, els) -> Ite(f g, f thn, f els)
  | Unif(_) -> Unif
  | Flip(_, v) -> Flip(Bignum.to_float v)
  | Plus(_, e1, e2) -> Plus(f e1, f e2)
  | Mul(_, e1, e2) -> Mul(f e1, f e2)
  | Lt(_, e1, e2) -> Lt(f e1, f e2)
  | Or(_, e1, e2) -> Or(f e1, f e2)
  | And(_, e1, e2) -> And(f e1, f e2)
  | Not(_, e1) -> Not(f e1)
  | Return(_, e) -> Return(f e)

(** convert an external program into a core program *)
let from_external_program (e: Syntax.program) = 
  { body = (from_external_expr e.body) }
