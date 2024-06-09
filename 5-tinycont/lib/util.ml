(** some generic utility functions used in different parts of the library *)

open Lexing

let colnum pos =
  (pos.pos_cnum - pos.pos_bol) - 1

let pos_string pos =
  let l = string_of_int pos.pos_lnum
  and c = string_of_int ((colnum pos) + 1) in
  "line " ^ l ^ ", column " ^ c

let parse' f s =
  let lexbuf = Lexing.from_string s in
  try
    f Lexer.token lexbuf
  with Parser.Error ->
    raise (Failure ("Parse error at " ^ (pos_string lexbuf.lex_curr_p)))

(** parse a string into program syntax *)
let parse_program s =
  parse' Parser.program s

(** read `filename` into a string *)
let read_whole_file filename =
  (* open_in_bin works correctly on Unix and Windows *)
  let ch = open_in_bin filename in
  let s = really_input_string ch (in_channel_length ch) in
  close_in ch;
  s

(** parse a program from a filename into an AST *)
let parse_from_file filename =
  read_whole_file filename
  |> parse_program


let rng = Gsl.Rng.make (Gsl.Rng.default ())

(** draws a random value from a uniform between [l, u] inclusively *)
let sample_uniform (l: float) (u: float) = 
  assert (l < u);
  (Random.float (u -. l)) +. l

let sample_bool (theta: float) : bool = 
  (Random.float 1.0) < theta