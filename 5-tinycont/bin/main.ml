(** main entry point *)
open Cont
open Util

(***********************************************************************************)
(* command line arguments                                                          *)
(* see https://dev.realworldocaml.org/command-line-parsing.html                    *)
(***********************************************************************************)



(** print the s-expression parsing of the program (mainly for debugging the parser )*)
let _print_sexp fname =
  (* read the fname into a string *)
  let s = read_whole_file fname in
  let parsed_program = parse_program s in
  Format.printf "%s" (Sexplib0__Sexp.to_string_hum (Syntax.sexp_of_program parsed_program));
  ()

let command =
  Command.basic
    ~summary:"Perform inference an input file"
    ~readme:(fun () -> "")
    (let open Command.Let_syntax in
     let open Command.Param in
     let%map filename = anon ("filename" %: string)
     and num_samples = flag "-n" (required int) ~doc:"Number of samples" in
     fun () ->
        let parsed = parse_from_file filename in
        let internal = Core_grammar.from_external_program parsed in
        (* uncomment to print AST *)
        (* Format.printf "parsed: %s" (Sexplib.Sexp.to_string_hum (Core_grammar.sexp_of_program internal)); *)
        let estimate = Direct_sampling.estimate internal num_samples in
        Format.printf "Estimate: %f\n" estimate)

let () = Command_unix.run ~version:"1.0" ~build_info:"RWO" command
