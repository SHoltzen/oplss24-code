(** a tiny BDD implementation *)

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

