(** a very expressive PPL: all the features you want!
    this language has mutable state, references, random sampling, general
    recursion, etc.
*)

type expr =
  | True
  | False
  | Num of int
  | And of expr * expr
  | Or of expr * expr
  | Not of expr
  | Ite of expr * expr * expr
  | Plus of expr * expr
  | Lt of expr * expr
  | Lam of string * expr
  | App of expr * expr
  | Ref of expr
  | Deref of expr
  | Set of expr * expr
  | Let of string * expr * expr
  | Begin of expr list
  | Letrec of { binding: string; lam_arg: string; lam_body: expr; body: expr }
  | Ident of string
  | Flip of float
  | Observe of expr * expr

type loc = int

module StringMap = Map.Make(String)

type value =
  | VInt of int
  | VBool of bool
  | VLoc of int
  | VLam of ( value StringMap.t) * string * expr

type env = value StringMap.t

type store = {
  table: (loc, value) Hashtbl.t;
  next_free: int ref
}

let new_store () = { table = Hashtbl.create 100; next_free = ref 0 }

let fresh_loc (s:store) : loc =
  let l = !(s.next_free) in
  s.next_free := l + 1;
  l

let set_store (s:store) l v = Hashtbl.add s.table l v

let get_store (s:store) l = Hashtbl.find s.table l

let cur_c = ref 0

let fresh_name () =
  cur_c := !cur_c + 1;
  Format.sprintf "fresh_%d" !cur_c

exception Runtime of string

let rec sample (s:store) (env:env) (e:expr) : value option =
  match e with
  | True -> Some(VBool(true))
  | False -> Some(VBool(false))
  | Num(n) -> Some(VInt(n))
  | Ident(x) ->
    (match StringMap.find_opt x env with
     | Some(v) -> Some(v)
     | None -> raise (Runtime(Format.sprintf "ident not found: %s" x)))
  | And(e1, e2) ->
    (match (sample s env e1, sample s env e2) with
     | Some(VBool(b1)), Some(VBool(b2)) -> Some(VBool(b1 && b2))
     | _ -> None)
  | Or(e1, e2) ->
    (match (sample s env e1, sample s env e2) with
     | Some(VBool(b1)), Some(VBool(b2)) -> Some(VBool(b1 || b2))
     | _ -> None)
  | Not(e1) ->
    (match sample s env e1 with
     | Some(VBool(b1)) -> Some(VBool(not b1))
     | _ -> None)
  | Ite(g, thn, els) ->
    (match (sample s env g, sample s env thn, sample s env els) with
     | Some(VBool(sg)), Some(VBool(sthn)), Some(VBool(sels)) ->
       Some(VBool(if sg then sthn else sels))
     | None, _, _ | _, None, _ | _, _, None -> None
     | _ -> failwith "Type error")
  | Plus(e1, e2) ->
    (match (sample s env e1, sample s env e2) with
     | Some(VInt(b1)), Some(VInt(b2)) -> Some(VInt(b1 + b2))
     | (None, _) | (_, None) -> None
     | _ -> failwith "type error")
  | Lt(e1, e2) ->
    (match (sample s env e1, sample s env e2) with
     | Some(VInt(b1)), Some(VInt(b2)) -> Some(VBool(b1 < b2))
     | (None, _) | (_, None) -> None
     | _ -> failwith "type error")
  | Lam(x, body) -> Some(VLam(env, x, body))
  | App(e1, e2) ->
    (match sample s env e1, sample s env e2 with
     | Some(VLam(closure, x, body)), Some(v2) ->
       let new_env = StringMap.add x v2 closure in
       sample s new_env body
     | _ -> None)
  | Ref(e) ->
    Option.bind (sample s env e) (fun v ->
        let l = fresh_loc s in
        set_store s l v;
        Some(VLoc(l)))
  | Deref(e) ->
    (match sample s env e with
     | Some(VLoc(l)) -> Some(get_store s l)
     | _ -> None )
  | Set(e1, e2) ->
    (match (sample s env e1), (sample s env e2) with
     | Some(VLoc(l)), Some(v) ->
       set_store s l v;
       Some(VBool(true))
     | _, None | None, _ -> None
     | _ -> failwith "Type error")
  | Begin([hd]) -> sample s env hd
  | Begin(e :: rst) ->
    Option.bind (sample s env e) (fun _ -> sample s env (Begin(rst)))
  | Begin([]) -> raise (Runtime("invalid begin with no body"))
  | Let(x, e1, e2) ->
    (match sample s env e1 with
     | Some(v) ->
       let new_env = StringMap.add x v env in
       sample s new_env e2
     | _ -> None )
  | Letrec {binding; lam_arg; lam_body; body} ->
    (* implement letrec using Landin's knot *)
    (* for example:
       letrec f (fun x -> f x) (f true)
       -- macro expands to -->
       let tmp = ref 0 in
       let f = fun x -> !tmp x in
       let f = fun x -> f x in
       tmp := f;
       f true
    *)
    (* store in the environment a lambda that invokes the reference *)
    let tmp = fresh_name () in
    let new_term = Let(tmp, Ref(Num(0)),
                      Let(binding, Lam("x", App(Deref(Ident(tmp)), Ident("x"))),
                         Let(binding, Lam(lam_arg, lam_body),
                            Begin([Set(Ident(tmp), Ident(binding));
                                   body])))) in
    sample s env new_term
  | Flip(f) ->
    if (Random.float 1.0 < f) then Some(VBool(true)) else Some(VBool(false))
  | Observe(e1, e2) ->
    (match sample s env e1 with
     | Some(VBool(true)) -> sample s env e2
     | _ -> None)

let estimate (e:expr) (v:value) (num_samples: int) : float =
  let count = ref 0.0 in
  let accepted = ref 0.0 in
  for _ = 0 to num_samples do
    match sample (new_store ()) (StringMap.empty) e with
    | Some(sampled_v) ->
      accepted := !accepted +. 1.0;
      if sampled_v = v then count := !count +. 1.0 else ()
    | None -> ()
  done;
  (!count /. !accepted)


(**********************************************************************************)
(** This module is a very simple parsing library for S-expressions. *)
(* Copyright (C) 2009  Florent Monnier, released under MIT license. *)

type sexpr = Atom of string | Expr of sexpr list

type state =
  | Parse_root of sexpr list
  | Parse_content of sexpr list
  | Parse_word of Buffer.t * sexpr list
  | Parse_string of bool * Buffer.t * sexpr list

let parse pop_char =
  let rec aux st =
    match pop_char() with
    | None ->
        begin match st with
        | Parse_root sl -> (List.rev sl)
        | Parse_content _
        | Parse_word _
        | Parse_string _ ->
            failwith "Parsing error: content not closed by parenthesis"
        end
    | Some c ->
        match c with
        | '(' ->
            begin match st with
            | Parse_root sl ->
                let this = aux(Parse_content []) in
                aux(Parse_root((Expr this)::sl))
            | Parse_content sl ->
                let this = aux(Parse_content []) in
                aux(Parse_content((Expr this)::sl))
            | Parse_word(w, sl) ->
                let this = aux(Parse_content []) in
                aux(Parse_content((Expr this)::Atom(Buffer.contents w)::sl))
            | Parse_string(_, s, sl) ->
                Buffer.add_char s c;
                aux(Parse_string(false, s, sl))
            end
        | ')' ->
            begin match st with
            | Parse_root sl ->
                failwith "Parsing error: closing parenthesis without openning"
            | Parse_content sl -> (List.rev sl)
            | Parse_word(w, sl) -> List.rev(Atom(Buffer.contents w)::sl)
            | Parse_string(_, s, sl) ->
                Buffer.add_char s c;
                aux(Parse_string(false, s, sl))
            end
        | ' ' | '\n' | '\r' | '\t' ->
            begin match st with
            | Parse_root sl -> aux(Parse_root sl)
            | Parse_content sl -> aux(Parse_content sl)
            | Parse_word(w, sl) -> aux(Parse_content(Atom(Buffer.contents w)::sl))
            | Parse_string(_, s, sl) ->
                Buffer.add_char s c;
                aux(Parse_string(false, s, sl))
            end
        | '"' ->
            (* '"' *)
            begin match st with
            | Parse_root _ -> failwith "Parse error: double quote at root level"
            | Parse_content sl ->
                let s = Buffer.create 74 in
                aux(Parse_string(false, s, sl))
            | Parse_word(w, sl) ->
                let s = Buffer.create 74 in
                aux(Parse_string(false, s, Atom(Buffer.contents w)::sl))
            | Parse_string(true, s, sl) ->
                Buffer.add_char s c;
                aux(Parse_string(false, s, sl))
            | Parse_string(false, s, sl) ->
                aux(Parse_content(Atom(Buffer.contents s)::sl))
            end
        | '\\' ->
            begin match st with
            | Parse_string(true, s, sl) ->
                Buffer.add_char s c;
                aux(Parse_string(false, s, sl))
            | Parse_string(false, s, sl) ->
                aux(Parse_string(true, s, sl))
            | _ ->
                failwith "Parsing error: escape character in wrong place"
            end
        | _ ->
            begin match st with
            | Parse_root _ ->
                failwith(Printf.sprintf "Parsing error: char '%c' at root level" c)
            | Parse_content sl ->
                let w = Buffer.create 16 in
                Buffer.add_char w c;
                aux(Parse_word(w, sl))
            | Parse_word(w, sl) ->
                Buffer.add_char w c;
                aux(Parse_word(w, sl))
            | Parse_string(_, s, sl) ->
                Buffer.add_char s c;
                aux(Parse_string(false, s, sl))
            end
  in
  aux (Parse_root [])


let string_pop_char str =
  let len = String.length str in
  let i = ref(-1) in
  (function () -> incr i; if !i >= len then None else Some(str.[!i]))


let parse_string str =
  parse (string_pop_char str)


let ic_pop_char ic =
  (function () ->
     try Some(input_char ic)
     with End_of_file -> (None))


let parse_ic ic =
  parse (ic_pop_char ic)


let parse_file filename =
  let ic = open_in filename in
  let res = parse_ic ic in
  close_in ic;
  (res)


let quote s =
  "\"" ^ s ^ "\""

let needs_quote s =
  List.exists (String.contains s) [' '; '\n'; '\r'; '\t'; '('; ')']

let protect s =
  let s = String.escaped s in
  if needs_quote s then quote s else s


let string_of_sexpr s =
  let rec aux acc = function
  | (Atom tag)::tl -> aux ((protect tag)::acc) tl
  | (Expr e)::tl ->
      let s =
        "(" ^
        (String.concat " " (aux [] e))
        ^ ")"
      in
      aux (s::acc) tl
  | [] -> (List.rev acc)
  in
  String.concat " " (aux [] s)


let print_sexpr s =
  print_endline (string_of_sexpr s)


let string_of_sexpr_indent s =
  let rec aux i acc = function
  | (Atom tag)::tl -> aux i ((protect tag)::acc) tl
  | (Expr e)::tl ->
      let s =
        "\n" ^ (String.make i ' ') ^ "(" ^
        (String.concat " " (aux (succ i) [] e))
        ^ ")"
      in
      aux i (s::acc) tl
  | [] -> (List.rev acc)
  in
  String.concat "\n" (aux 0 [] s)


let print_sexpr_indent s =
  print_endline (string_of_sexpr_indent s)

(**********************************************************************************)
(* s-expression parser *)

exception Parse_error of string

(** true if s is a number *)
let str_is_num s =
  try int_of_string s |> ignore; true
  with Failure _ -> false

(** parse an s-expression into a pure tinyppl program *)
let rec e_of_sexpr (s:sexpr) : expr =
  match s with
  | Atom(s) when s = "true" -> True
  | Atom(s) when s = "false" -> False
  | Atom(s) when str_is_num s -> Num(int_of_string s)
  | Atom(s) -> Ident(s)
  | Expr(Atom(s) :: snd :: []) when s = "!" -> Not(e_of_sexpr snd)
  | Expr(Atom(s) :: snd :: thrd :: []) when s = "and" ->
    And(e_of_sexpr snd, e_of_sexpr thrd)
  | Expr(Atom(s) :: snd :: thrd :: []) when s = "or" ->
    Or(e_of_sexpr snd, e_of_sexpr thrd)
  | Expr(Atom(s) :: snd :: thrd :: []) when s = "+" ->
    Plus(e_of_sexpr snd, e_of_sexpr thrd)
  | Expr(Atom(s) :: snd :: thrd :: []) when s = "<" ->
    Lt(e_of_sexpr snd, e_of_sexpr thrd)
  | Expr(Atom(s) :: g :: thn :: els :: []) when s = "if" ->
    Ite(e_of_sexpr g, e_of_sexpr thn, e_of_sexpr els)
  | Expr(Atom(s) :: Atom(x) :: body :: []) when s = "lam" ->
    Lam(x, e_of_sexpr body)
  | Expr(Atom(s) :: Atom(x) :: e1 :: e2 :: []) when s = "let" ->
    Let(x, e_of_sexpr e1, e_of_sexpr e2)
  | Expr(Atom(s) :: Atom(x) :: Expr(Atom(lam) :: Atom(inner) :: body :: []) :: e2 :: []) when s = "letrec" && lam = "lam" ->
    Letrec { binding = x; lam_arg = inner; lam_body = e_of_sexpr body; body = e_of_sexpr e2}
  | Expr(Atom(f) :: Atom(r) :: []) when f = "flip" ->
    Flip(Float.of_string r)
  | Expr(Atom(s) :: snd :: thrd :: []) when s = "observe" ->
    Observe(e_of_sexpr snd, e_of_sexpr thrd)
  | Expr(e1 :: e2 :: []) -> App(e_of_sexpr e1, e_of_sexpr e2)
  | _ -> raise (Parse_error(string_of_sexpr [s]))

(** parse a string into a tinyppl expression *)
let e_of_string s : expr =
  let sexpr = parse_string s in
  e_of_sexpr (List.hd sexpr)

let within_epsilon a b = Float.abs (a -. b) < 0.01

(* some examples *)
let p1 = e_of_string "(let x (flip 0.5) x)"

let p2 = e_of_string "(let x (flip 0.5)
                        (let y (flip 0.4)
                        (let z (flip 0.6)
                        (if x y z))))"

let p3 = e_of_string "(let x (flip 0.5)
                        (let y (flip 0.5)
                        (observe (or x y)
                        x)))"

let p4 = e_of_string "(let x (lam y (flip 0.2))
                         (let f1 (x true)
                            f1))"

let p5 = e_of_string "(let x (lam y (flip 0.2))
                         (let f1 (x true)
                            (let f2 (x true)
                              (and f1 f2))))"


let p6 = e_of_string "(letrec geom (lam x (if (flip 0.5) (+ 1 (geom true)) 1))
                         (let sum (geom true) (< sum 4)))"

let p7 = e_of_string "(letrec foo (lam x (if false (foo (+ x 1)) x)) (foo 100))"

let p8 = e_of_string "(let x (ref 0) )"

let () =
  assert (within_epsilon (estimate p1 (VBool(true)) 10000) 0.5);
  assert (within_epsilon (estimate p2 (VBool(true)) 10000) 0.5);
  assert (within_epsilon (estimate p3 (VBool(true)) 30000) 0.666666);
  assert (within_epsilon (estimate p4 (VBool(true)) 30000) 0.2);
  assert (within_epsilon (estimate p5 (VBool(true)) 30000) 0.04)
