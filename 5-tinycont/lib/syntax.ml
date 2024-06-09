(**
   Public-facing grammar. This is the parser target.
*)

open Sexplib.Std

(* this syntax is a bit weird. it is necessary because Lexing.position does not
   by default derive sexp. *)
type lexing_position =
  Lexing.position =
  { pos_fname : string
  ; pos_lnum : int
  ; pos_bol : int
  ; pos_cnum : int
  }
[@@deriving sexp]

(** contains information necessary for referring to line numbers
   in the source file *)
type source = {startpos: lexing_position; endpos: lexing_position}
[@@deriving sexp_of]


(** core external grammar *)
type eexpr =
  | Ident   of source * string
  | Real    of source * Bignum.t
  | Bool    of source * bool
  | Return  of source * eexpr
  | Observe of source * eexpr * eexpr
  | Bind    of source * string * eexpr * eexpr
  | Ite     of source * eexpr * eexpr * eexpr
  | Unif    of source
  | Flip    of source * Bignum.t
  | Plus    of source * eexpr * eexpr 
  | Lt      of source * eexpr * eexpr  (* less-than *)
  | Or      of source * eexpr * eexpr 
  | Mul     of source * eexpr * eexpr 
  | And     of source * eexpr * eexpr 
  | Not     of source * eexpr
[@@deriving sexp_of]

(** top-level symbol *)
type program = { body: eexpr }
[@@deriving sexp_of]

exception Type_error of String.t

let gen_src =
  let gen_pos = { Lexing.dummy_pos with pos_fname = "<generated>" } in
  { startpos = gen_pos; endpos = gen_pos }

