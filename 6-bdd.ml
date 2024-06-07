(** a tiny BDD implementation *)

type bdd_ptr = int

(** tiny bdd *)
type bdd =
  True
  | False
  | Node of { topvar: int; low: bdd_ptr; high: bdd_ptr }

type bdd_table = {
  (* backing table that stores all unique BDDs *)
  backing_table: bdd Array.t;

  (* memoizes BDDs to ensure there is only ever 1 unique BDD pointer for a
     particular structural BDD form *)
  compute_table: (bdd, int) Hashtbl.t;

  (* holds the next free location in the backing table*)
  next_free: int ref;

  (* number of variables that have been allocated so far *)
  num_vars: int ref;

  (* memoizes BDD conjunction operations *)
  memo_table: (bdd_ptr * bdd_ptr, bdd_ptr) Hashtbl.t
}

let true_ptr = 0

let false_ptr = 1

let fresh_bdd_table () : bdd_table =
  let arr = Array.make 10000 True in
  let compute_table = Hashtbl.create 100 in
  Hashtbl.add compute_table true_ptr True;
  Hashtbl.add compute_table false_ptr False;
  Array.set arr 1 False;
  Array.set arr 0 True;
  {
    backing_table=arr;
    next_free = ref 2;
    num_vars = ref 0;
    compute_table = Hashtbl.create 100;
    memo_table = Hashtbl.create 100;
  }

let deref_bdd (tbl:bdd_table) (ptr:bdd_ptr) : bdd =
  Array.get tbl.backing_table ptr

(** get or insert a fresh bdd into the table *)
let get_or_insert (table:bdd_table) (bdd:bdd) : bdd_ptr =
  match Hashtbl.find_opt table.compute_table bdd with
  | Some(v) -> v
  | None ->
    let new_idx = !(table.next_free) in
    table.next_free := new_idx + 1;
    Array.set table.backing_table new_idx bdd;
    Hashtbl.add table.compute_table bdd new_idx;
    new_idx

let rec string_of_bdd (tbl: bdd_table) (f:bdd_ptr) : string =
  match deref_bdd tbl f with
  | True -> "T"
  | False -> "F"
  | Node { topvar; low; high } ->
    Format.sprintf "(%d %s %s)" topvar (string_of_bdd tbl low) (string_of_bdd tbl high)

(** get a pointer to a fresh BDD variable that is true *)
let fresh_var (tbl: bdd_table) : bdd_ptr =
  let fresh_var = !(tbl.num_vars) in
  tbl.num_vars := fresh_var + 1;
  get_or_insert tbl (Node { topvar = fresh_var; low = true_ptr; high = false_ptr})

(** get a pointer to a bdd with topvariable `topvar` *)
let bdd_var (tbl: bdd_table) (topvar: int) : bdd_ptr =
  (* assert that this variable has been allocated via freshvar; this invariant
     is necessary to ensure that freshvar always produces a variable with no existing
     references
  *)
  assert (topvar < !(tbl.num_vars));
  get_or_insert tbl (Node { topvar = topvar; low = true_ptr; high = false_ptr})


(** negate a BDD *)
let rec neg (tbl:bdd_table) (f:bdd_ptr) : bdd_ptr =
  match deref_bdd tbl f with
  | True -> false_ptr
  | False -> true_ptr
  | Node { topvar; low; high } ->
    get_or_insert tbl (Node { topvar; low = neg tbl low; high = neg tbl high})

(** conjoin together two BDDs *)
let rec bdd_and (tbl:bdd_table) (f:bdd_ptr) (g:bdd_ptr) : bdd_ptr =
  match (deref_bdd tbl f), (deref_bdd tbl g) with
  | _, False
  | False, _ -> false_ptr
  | True, True -> true_ptr
  | True, Node { topvar; high; low } -> g
  | Node { topvar; high; low }, True -> f
  | Node { topvar=f_topvar; low=f_low; high=f_high },
    Node { topvar=g_topvar; low=g_low; high=g_high } when f_topvar = g_topvar ->
    let l = bdd_and tbl f_low g_low in
    let h = bdd_and tbl f_high g_high in
    if l = h then l else get_or_insert tbl (Node { topvar = f_topvar; low = l; high = h})
  | Node { topvar=f_topvar; low=f_low; high=f_high },
    Node { topvar=g_topvar; low=g_low; high=g_high } ->
    if f_topvar < g_topvar then
      let l = bdd_and tbl f_low g in
      let h = bdd_and tbl f_high g in
      if l = h then l else get_or_insert tbl (Node { topvar = f_topvar; low = l; high = h})
    else
      let l = bdd_and tbl f g_low in
      let h = bdd_and tbl f g_high in
      if l = h then l else get_or_insert tbl (Node { topvar = g_topvar; low = l; high = h})


(* some simple tests *)
let () =
  (* test for canonicity of negation *)
  let tbl = fresh_bdd_table () in
  let b1 = fresh_var tbl in
  let b1n = neg tbl b1 in
  let b2n = neg tbl b1 in
  assert (b1n = b2n)

let () =
  (* test for canonicity of conjunction *)
  let tbl = fresh_bdd_table () in
  let a = fresh_var tbl in
  let b = fresh_var tbl in
  let a2 = bdd_var tbl 0 in
  let b2 = bdd_var tbl 1 in
  assert (bdd_and tbl a b = bdd_and tbl b2 a2)
