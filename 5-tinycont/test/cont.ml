(** https://dev.realworldocaml.org/testing.html *)

open OUnit2
open Cont


(** given an input string s, give an estimate that results from drawing n 
samples *)
let sample_program s n = 
  let parsed = Util.parse_program s in
  let internal = Core_grammar.from_external_program parsed in
  Direct_sampling.estimate internal n

let prog_1 = "
x <- unif;
return x < 0.5
"


let prog_sum = "
x <- unif;
y <- unif;
return (x + y < 1.0)
"


let prog_if = "
x <- unif;
mul <- return x * 10;
if mul < 5 then flip 0.2 else flip 0.8
"

let simple_obs = "
x <- unif;
observe x < 0.5;
return x < 0.25
"

let simple_obs_2 = "
x <- flip 0.5;
y <- flip 0.5;
observe x || y;
return x
"

(** true if a and b are within 0.00001 *)
let within_epsilon a b = Float.abs(a -. b) < 0.1

let assert_prog prog ans =
  let prog_answer = sample_program prog 100000 in
  assert_bool (Format.sprintf "Incorrect inference result for %s\nExpected %f got %f" prog ans prog_answer) 
    (within_epsilon prog_answer ans)

let tests = "importance_sampling" >::: [
  "basic" >:: (fun _ -> assert_prog prog_1 0.5);
  "basic_sum" >:: (fun _ -> assert_prog prog_sum 0.5);
  "basic_if" >:: (fun _ -> assert_prog prog_if 0.5);
  "basic_obs" >:: (fun _ -> assert_prog simple_obs 0.5);
  "basic_obs_discrete" >:: (fun _ -> assert_prog simple_obs_2 0.66666);
]

let _ = Random.self_init ()
let _ = run_test_tt_main tests
