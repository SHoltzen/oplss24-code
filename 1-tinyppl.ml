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
  | Flip(f) -> if v then f else (1.0 -. f)
  | Bind(x, e1, e2) ->
    let true_env = StringMap.add x true env in
    let false_env = StringMap.add x false env in
    let prob_e1_t = prob e1 env true in
    let prob_e1_f = prob e1 env false in
    (prob_e1_t *. (prob e2 true_env v)) +. (prob_e1_f *. (prob e2 false_env v))
  | Return(p) ->
    if (pure_eval p env) = v then 1.0 else 0.0

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
(* s-expression parser for TinyPPL *)

exception Parse_error of string

(** parse an s-expression into a pure tinyppl program *)
let rec tinyppl_p_of_sexpr (s:sexpr) : pure_e =
  match s with
  | Atom(s) when s = "true" -> True
  | Atom(s) when s = "false" -> False
  | Atom(s) -> Ident(s)
  | Expr(Atom(s) :: snd :: []) when s = "not" -> Not(tinyppl_p_of_sexpr snd)
  | Expr(Atom(s) :: snd :: thrd :: []) when s = "and" ->
    And(tinyppl_p_of_sexpr snd, tinyppl_p_of_sexpr thrd)
  | Expr(Atom(s) :: snd :: thrd :: []) when s = "or" ->
    Or(tinyppl_p_of_sexpr snd, tinyppl_p_of_sexpr thrd)
  | Expr(Atom(s) :: g :: thn :: els :: []) when s = "if" ->
    Ite(tinyppl_p_of_sexpr g, tinyppl_p_of_sexpr thn, tinyppl_p_of_sexpr els)
  | _ -> raise (Parse_error (string_of_sexpr [s]))

(** parse a string into a pure tinyppl program *)
let tinyppl_p_of_string s : pure_e =
  let sexpr = parse_string s in
  tinyppl_p_of_sexpr (List.hd sexpr)

let rec tinyppl_e_of_sexpr (s:sexpr) : expr =
  match s with
  | Expr(Atom(f) :: Atom(r) :: []) when f = "flip" ->
    Flip(Float.of_string r)
  | Expr(Atom(r) :: e :: []) when r = "return" -> Return(tinyppl_p_of_sexpr e)
  | Expr(Atom(s) :: Atom(x) :: e1 :: e2 :: []) when s = "bind" ->
    Bind(x, tinyppl_e_of_sexpr e1, tinyppl_e_of_sexpr e2)
  | _ -> raise (Parse_error (string_of_sexpr [s]))

(** parse a string into a tinyppl expression *)
let tinyppl_e_of_string s : expr =
  let sexpr = parse_string s in
  tinyppl_e_of_sexpr (List.hd sexpr)

(* some examples *)
let p1 = tinyppl_e_of_string "(bind x (flip 0.5) (return x))"

let p2 = tinyppl_e_of_string "(bind x (flip 0.5)
                              (bind y (flip 0.4)
                              (bind z (flip 0.6)
                              (return (if x y z)))))"

let network = tinyppl_e_of_string
  "(bind r2forward (flip 0.5)
   (bind l1fail (flip 0.02)
   (bind l2fail (flip 0.02)
   (bind l3fail (flip 0.02)
   (bind l4fail (flip 0.02)
   (return (if r2forward (and (not l1fail) (not l4fail))
                         (and (not l2fail) (not l3fail)))))))))"

let () =
  assert (within_epsilon (prob p1 StringMap.empty true) 0.5);
  assert (within_epsilon (prob p2 StringMap.empty true) 0.5)
