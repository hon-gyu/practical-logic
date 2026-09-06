(* Tests for the atp library. *)

open Atp
open Lib
open Formulas
open Prop
open Fol

(* Harness
   ======= *)

let failures = ref 0
let checks = ref 0

let check name ok =
  incr checks;
  if not ok then begin
    incr failures;
    Printf.printf "FAIL %s\n" name
  end

let check_eq name ~expected ~actual to_string =
  incr checks;
  if expected <> actual then begin
    incr failures;
    Printf.printf "FAIL %s\n  expected: %s\n  actual:   %s\n" name
      (to_string expected) (to_string actual)
  end

let string_of_int_list l = "[" ^ String.concat "; " (List.map string_of_int l) ^ "]"

(* Harrison's printers write to Format's standard formatter, so capturing
   their output means redirecting it rather than using a string formatter. *)
let capture f =
  let buf = Buffer.create 256 in
  let saved = Format.get_formatter_out_functions () in
  Format.print_flush ();
  Format.set_formatter_out_functions
    { Format.out_string = (fun s pos len -> Buffer.add_substring buf s pos len);
      out_flush = ignore;
      out_newline = (fun () -> Buffer.add_char buf '\n');
      out_spaces = (fun n -> Buffer.add_string buf (String.make n ' '));
      out_indent = (fun n -> Buffer.add_string buf (String.make n ' ')) };
  Fun.protect
    ~finally:(fun () ->
      Format.print_flush ();
      Format.set_formatter_out_functions saved)
    f;
  Buffer.contents buf

let printed_fol fm = capture (fun () -> print_fol_formula fm)

(* Tableaux.tab and Meson.meson trace their search on the standard formatter; swallow it so
   the test output stays readable. *)
let quietly f x = let r = ref None in ignore (capture (fun () -> r := Some (f x))); Option.get !r

(* lib.ml
   ====== *)

let test_lib () =
  check_eq "setify sorts and dedups"
    ~expected:[1; 2; 3] ~actual:(setify [3; 1; 2; 1; 3]) string_of_int_list;
  check_eq "subtract"
    ~expected:[1; 3] ~actual:(subtract [1; 2; 3] [2; 4]) string_of_int_list;
  check "can" (can (fun x -> List.hd x) [1] && not (can List.hd []))

(* Quotations and printing (formulas.ml, fol.ml)
   ============================================= *)

let test_quotations () =
  check "fml quotation parses to the expected term"
    (match {%fol|p ==> q|} with
     | Imp (Atom (R ("p", [])), Atom (R ("q", []))) -> true
     | _ -> false);
  check "tm quotation parses to the expected term"
    (match {%tm|x + y|} with
     | Fn ("+", [Var "x"; Var "y"]) -> true
     | _ -> false);
  check_eq "printing round-trips through the parser"
    ~expected:"<<p ==> q>>" ~actual:(printed_fol {%fol|p ==> q|}) (fun s -> s);
  check_eq "printing drops redundant brackets"
    ~expected:"<<forall x. p(x) ==> q(x)>>"
    ~actual:(printed_fol {%fol|forall x. (p(x) ==> q(x))|}) (fun s -> s)

(* Propositional logic (prop.ml, dp.ml)
   ==================================== *)

let test_prop () =
  check "excluded middle is a tautology" (tautology {%fol|p \/ ~p|});
  check "p ==> q is not a tautology" (not (tautology {%fol|p ==> q|}));
  check "peirce" (tautology {%fol|((p ==> q) ==> p) ==> p|});
  check "dnf preserves meaning"
    (let fm = {%fol|(p \/ q /\ r) /\ (~p \/ ~r)|} in
     tautology (Iff (fm, dnf fm)));
  check "cnf preserves meaning"
    (let fm = {%fol|(p \/ q /\ r) /\ (~p \/ ~r)|} in
     tautology (Iff (fm, cnf fm)));
  check "psimplify"
    (psimplify {%fol|true ==> (p <=> (p <=> false))|} = {%fol|p <=> ~p|});
  (* Dp.dptaut and Dp.dplltaut go through defcnf, which is propositional only, so
     these use parse_prop_formula rather than the quotation: after fol.ml the
     {%fol|...|} parser is the first-order one. *)
  let peirce = parse_prop_formula "((p ==> q) ==> p) ==> p" in
  check "dptaut agrees with tautology" (Dp.dptaut peirce);
  check "dplltaut agrees with tautology" (Dp.dplltaut peirce)

(* First-order logic (unif.ml, skolem.ml, tableaux.ml, meson.ml)
   ============================================================= *)

let test_fol () =
  check "unify_and_apply solves a simple equation"
    (Unif.unify_and_apply [{%tm|f(x,g(y))|}, {%tm|f(f(z),w)|}]
     = [{%tm|f(f(z),g(y))|}, {%tm|f(f(z),g(y))|}]);
  check "unify_and_apply rejects an occurs-check failure"
    (not (can Unif.unify_and_apply [{%tm|f(x,g(y))|}, {%tm|f(y,x)|}]));
  check "skolemize removes existentials"
    (Skolem.skolemize {%fol|exists y. x < y ==> forall u. exists v. x * u < y * v|}
     = {%fol|~x < f_y(x) \/ x * u < f_y(x) * f_v(u,x)|});
  check "tab proves a valid formula"
    (can (quietly Tableaux.tab) {%fol|(forall x. p(x) ==> q(x)) /\ p(a) ==> q(a)|});
  check "meson proves Pelletier 18"
    (can (quietly Meson.meson) {%fol|exists y. forall x. p(y) ==> p(x)|})

(* Decision procedures (cooper.ml)
   =============================== *)

let test_qelim () =
  check "integer_qelim on a true statement"
    (Cooper.integer_qelim {%fol|forall x. exists y. x = 2 * y \/ x = 2 * y + 1|}
     = {%fol|true|});
  check "integer_qelim on a false statement"
    (Cooper.integer_qelim {%fol|exists x. 2 * x = 1|} = {%fol|false|})

(* Main
   ==== *)

let () =
  Initialization.init ();
  test_lib ();
  test_quotations ();
  test_prop ();
  test_fol ();
  test_qelim ();
  Printf.printf "%d checks, %d failures\n" !checks !failures;
  if !failures > 0 then exit 1
