open Lib
open Intro
open Formulas

(* Warnings the book's style trips in this file; the rest of the
   library compiles with them on.  See lib/dune. *)
[@@@warning "-8-32"]

(* ========================================================================= *)
(* Basic stuff for propositional logic: datatype, parsing and printing.      *)
(* ========================================================================= *)

type prop = P of string;;

let pname(P s) = s;;

(* ------------------------------------------------------------------------- *)
(* Parsing of propositional formulas.                                        *)
(* ------------------------------------------------------------------------- *)

let parse_propvar vs inp =
  match inp with
    p::oinp when p <> "(" -> Atom(P(p)),oinp
  | _ -> failwith "parse_propvar";;

let parse_prop_formula = make_parser
  (parse_formula ((fun _ _ -> failwith ""),parse_propvar) []);;

(* ------------------------------------------------------------------------- *)
(* Printer.                                                                  *)
(* ------------------------------------------------------------------------- *)

let print_propvar prec p = print_string(pname p);;

let print_prop_formula = print_qformula print_propvar;;


(* ------------------------------------------------------------------------- *)
(* Testing the parser and printer.                                           *)
(* ------------------------------------------------------------------------- *)


let%expect_test "eg: Testing the parser and printer" =
  let fm = {%prop|p ==> q <=> r /\ s \/ (t <=> ~ ~u /\ v)|} in
  print_prop_formula
    (fm);
  print_prop_formula
    (And(fm,fm));
  print_prop_formula
    (And(Or(fm,fm),fm));
  [%expect {| |}]
;;

(* ------------------------------------------------------------------------- *)
(* Interpretation of formulas.                                               *)
(* ------------------------------------------------------------------------- *)

let rec eval fm v =
  match fm with
    False -> false
  | True -> true
  | Atom(x) -> v(x)
  | Not(p) -> not(eval p v)
  | And(p,q) -> (eval p v) && (eval q v)
  | Or(p,q) -> (eval p v) || (eval q v)
  | Imp(p,q) -> not(eval p v) || (eval q v)
  | Iff(p,q) -> (eval p v) = (eval q v);;

let%expect_test "eg: use" =
  print_prop_formula
    (eval {%prop|p /\ q ==> q /\ r|}
         (function P"p" -> true | P"q" -> false | P"r" -> true));
  print_prop_formula
    (eval {%prop|p /\ q ==> q /\ r|}
         (function P"p" -> true | P"q" -> true | P"r" -> false));
  [%expect {| |}]
;;


(* ------------------------------------------------------------------------- *)
(* Return the set of propositional variables in a formula.                   *)
(* ------------------------------------------------------------------------- *)

let atoms fm = atom_union (fun a -> [a]) fm;;

let%expect_test "eg" =
  print_prop_formula
    (atoms {%prop|p /\ q \/ s ==> ~p \/ (r <=> s)|});
  [%expect {| |}]
;;


(* ------------------------------------------------------------------------- *)
(* Code to print out truth tables.                                           *)
(* ------------------------------------------------------------------------- *)

let rec onallvaluations subfn v ats =
  match ats with
    [] -> subfn v
  | p::ps -> let v' t q = if q = p then t else v(q) in
             onallvaluations subfn (v' false) ps &&
             onallvaluations subfn (v' true) ps;;

let print_truthtable fm =
  let ats = atoms fm in
  let width = itlist (max ** String.length ** pname) ats 5 + 1 in
  let fixw s = s^String.make(width - String.length s) ' ' in
  let truthstring p = fixw (if p then "true" else "false") in
  let mk_row v =
     let lis = map (fun x -> truthstring(v x)) ats
     and ans = truthstring(eval fm v) in
     print_string(itlist (^) lis ("| "^ans)); print_newline(); true in
  let separator = String.make (width * length ats + 9) '-' in
  print_string(itlist (fun s t -> fixw(pname s) ^ t) ats "| formula");
  print_newline(); print_string separator; print_newline();
  let _ = onallvaluations mk_row (fun x -> false) ats in
  print_string separator; print_newline();;

let%expect_test "eg" =
  print_prop_formula
    (print_truthtable {%prop|p /\ q ==> q /\ r|});
  let fm = {%prop|p /\ q ==> q /\ r|} in
  print_prop_formula
    (fm);
  print_prop_formula
    (print_truthtable fm);
  [%expect {| |}]
;;


(* ------------------------------------------------------------------------- *)
(* Additional examples illustrating formula classes.                         *)
(* ------------------------------------------------------------------------- *)

let%expect_test "eg: Additional examples illustrating formula classes" =
  print_prop_formula
    (print_truthtable {%prop|((p ==> q) ==> p) ==> p|});
  print_prop_formula
    (print_truthtable {%prop|p /\ ~p|});
  [%expect {| |}]
;;


(* ------------------------------------------------------------------------- *)
(* Recognizing tautologies.                                                  *)
(* ------------------------------------------------------------------------- *)

let tautology fm =
  onallvaluations (eval fm) (fun s -> false) (atoms fm);;

let%expect_test "eg: Examples" =
  print_prop_formula
    (tautology {%prop|p \/ ~p|});
  print_prop_formula
    (tautology {%prop|p \/ q ==> p|});
  print_prop_formula
    (tautology {%prop|p \/ q ==> q \/ (p <=> q)|});
  print_prop_formula
    (tautology {%prop|(p \/ q) /\ ~(p /\ q) ==> (~p <=> q)|});
  [%expect {| |}]
;;


(* ------------------------------------------------------------------------- *)
(* Related concepts.                                                         *)
(* ------------------------------------------------------------------------- *)

let unsatisfiable fm = tautology(Not fm);;

let satisfiable fm = not(unsatisfiable fm);;

(* ------------------------------------------------------------------------- *)
(* Substitution operation.                                                   *)
(* ------------------------------------------------------------------------- *)

let psubst subfn = onatoms (fun p -> tryapplyd subfn p (Atom p));;

let%expect_test "eg" =
  print_prop_formula
    (psubst (P"p" |=> {%prop|p /\ q|}) {%prop|p /\ q /\ p /\ q|});
  [%expect {| |}]
;;


(* ------------------------------------------------------------------------- *)
(* Surprising tautologies including Dijkstra's "Golden rule".                *)
(* ------------------------------------------------------------------------- *)

let%expect_test "eg: Surprising tautologies including Dijkstra's 'Golden rule'" =
  print_prop_formula
    (tautology {%prop|(p ==> q) \/ (q ==> p)|});
  print_prop_formula
    (tautology {%prop|p \/ (q <=> r) <=> (p \/ q <=> p \/ r)|});
  print_prop_formula
    (tautology {%prop|p /\ q <=> ((p <=> q) <=> p \/ q)|});
  print_prop_formula
    (tautology {%prop|(p ==> q) <=> (~q ==> ~p)|});
  print_prop_formula
    (tautology {%prop|(p ==> ~q) <=> (q ==> ~p)|});
  print_prop_formula
    (tautology {%prop|(p ==> q) <=> (q ==> p)|});
  (* ------------------------------------------------------------------------- *)
  (* Some logical equivalences allowing elimination of connectives.            *)
  (* ------------------------------------------------------------------------- *)
  print_prop_formula
    (forall tautology
     [{%prop|true <=> false ==> false|};
      {%prop|~p <=> p ==> false|};
      {%prop|p /\ q <=> (p ==> q ==> false) ==> false|};
      {%prop|p \/ q <=> (p ==> false) ==> q|};
      {%prop|(p <=> q) <=> ((p ==> q) ==> (q ==> p) ==> false) ==> false|}]);
  [%expect {| |}]
;;


(* ------------------------------------------------------------------------- *)
(* Dualization.                                                              *)
(* ------------------------------------------------------------------------- *)

let rec dual fm =
  match fm with
    False -> True
  | True -> False
  | Atom(p) -> fm
  | Not(p) -> Not(dual p)
  | And(p,q) -> Or(dual p,dual q)
  | Or(p,q) -> And(dual p,dual q)
  | _ -> failwith "Formula involves connectives ==> or <=>";;

let%expect_test "eg" =
  print_prop_formula
    (dual {%prop|p \/ ~p|});
  [%expect {| |}]
;;


(* ------------------------------------------------------------------------- *)
(* Routine simplification.                                                   *)
(* ------------------------------------------------------------------------- *)

let psimplify1 fm =
  match fm with
    Not False -> True
  | Not True -> False
  | Not(Not p) -> p
  | And(p,False) | And(False,p) -> False
  | And(p,True) | And(True,p) -> p
  | Or(p,False) | Or(False,p) -> p
  | Or(p,True) | Or(True,p) -> True
  | Imp(False,p) | Imp(p,True) -> True
  | Imp(True,p) -> p
  | Imp(p,False) -> Not p
  | Iff(p,True) | Iff(True,p) -> p
  | Iff(p,False) | Iff(False,p) -> Not p
  | _ -> fm;;

let rec psimplify fm =
  match fm with
  | Not p -> psimplify1 (Not(psimplify p))
  | And(p,q) -> psimplify1 (And(psimplify p,psimplify q))
  | Or(p,q) -> psimplify1 (Or(psimplify p,psimplify q))
  | Imp(p,q) -> psimplify1 (Imp(psimplify p,psimplify q))
  | Iff(p,q) -> psimplify1 (Iff(psimplify p,psimplify q))
  | _ -> fm;;

let%expect_test "eg" =
  print_prop_formula
    (psimplify {%prop|(true ==> (x <=> false)) ==> ~(y \/ false /\ z)|});
  print_prop_formula
    (psimplify {%prop|((x ==> y) ==> true) \/ ~false|});
  [%expect {| |}]
;;


(* ------------------------------------------------------------------------- *)
(* Some operations on literals.                                              *)
(* ------------------------------------------------------------------------- *)

let negative = function (Not p) -> true | _ -> false;;

let positive lit = not(negative lit);;

let negate = function (Not p) -> p | p -> Not p;;

(* ------------------------------------------------------------------------- *)
(* Negation normal form.                                                     *)
(* ------------------------------------------------------------------------- *)

let rec nnf fm =
  match fm with
  | And(p,q) -> And(nnf p,nnf q)
  | Or(p,q) -> Or(nnf p,nnf q)
  | Imp(p,q) -> Or(nnf(Not p),nnf q)
  | Iff(p,q) -> Or(And(nnf p,nnf q),And(nnf(Not p),nnf(Not q)))
  | Not(Not p) -> nnf p
  | Not(And(p,q)) -> Or(nnf(Not p),nnf(Not q))
  | Not(Or(p,q)) -> And(nnf(Not p),nnf(Not q))
  | Not(Imp(p,q)) -> And(nnf p,nnf(Not q))
  | Not(Iff(p,q)) -> Or(And(nnf p,nnf(Not q)),And(nnf(Not p),nnf q))
  | _ -> fm;;

(* ------------------------------------------------------------------------- *)
(* Roll in simplification.                                                   *)
(* ------------------------------------------------------------------------- *)

let nnf fm = nnf(psimplify fm);;

let%expect_test "eg: NNF function in action" =
  let fm = {%prop|(p <=> q) <=> ~(r ==> s)|} in
  print_prop_formula
    (fm);
  let fm' = nnf fm in
  print_prop_formula
    (fm');
  print_prop_formula
    (tautology(Iff(fm,fm')));
  [%expect {| |}]
;;

(* ------------------------------------------------------------------------- *)
(* Simple negation-pushing when we don't care to distinguish occurrences.    *)
(* ------------------------------------------------------------------------- *)

let rec nenf fm =
  match fm with
    Not(Not p) -> nenf p
  | Not(And(p,q)) -> Or(nenf(Not p),nenf(Not q))
  | Not(Or(p,q)) -> And(nenf(Not p),nenf(Not q))
  | Not(Imp(p,q)) -> And(nenf p,nenf(Not q))
  | Not(Iff(p,q)) -> Iff(nenf p,nenf(Not q))
  | And(p,q) -> And(nenf p,nenf q)
  | Or(p,q) -> Or(nenf p,nenf q)
  | Imp(p,q) -> Or(nenf(Not p),nenf q)
  | Iff(p,q) -> Iff(nenf p,nenf q)
  | _ -> fm;;

let nenf fm = nenf(psimplify fm);;

(* ------------------------------------------------------------------------- *)
(* Some tautologies remarked on.                                             *)
(* ------------------------------------------------------------------------- *)

let%expect_test "eg: Some tautologies remarked on" =
  print_prop_formula
    (tautology {%prop|(p ==> p') /\ (q ==> q') ==> (p /\ q ==> p' /\ q')|});
  print_prop_formula
    (tautology {%prop|(p ==> p') /\ (q ==> q') ==> (p \/ q ==> p' \/ q')|});
  [%expect {| |}]
;;


(* ------------------------------------------------------------------------- *)
(* Disjunctive normal form (DNF) via truth tables.                           *)
(* ------------------------------------------------------------------------- *)

let list_conj l = if l = [] then True else end_itlist mk_and l;;

let list_disj l = if l = [] then False else end_itlist mk_or l;;

let mk_lits pvs v =
  list_conj (map (fun p -> if eval p v then p else Not p) pvs);;

let rec allsatvaluations subfn v pvs =
  match pvs with
    [] -> if subfn v then [v] else []
  | p::ps -> let v' t q = if q = p then t else v(q) in
             allsatvaluations subfn (v' false) ps @
             allsatvaluations subfn (v' true) ps;;

let dnf fm =
  let pvs = atoms fm in
  let satvals = allsatvaluations (eval fm) (fun s -> false) pvs in
  list_disj (map (mk_lits (map (fun p -> Atom p) pvs)) satvals);;

let%expect_test "eg: Examples" =
  let fm = {%prop|(p \/ q /\ r) /\ (~p \/ ~r)|} in
  print_prop_formula
    (fm);
  print_prop_formula
    (dnf fm);
  print_prop_formula
    (print_truthtable fm);
  print_prop_formula
    (dnf {%prop|p /\ q /\ r /\ s /\ t /\ u \/ u /\ v|});
  [%expect {| |}]
;;

(* ------------------------------------------------------------------------- *)
(* DNF via distribution.                                                     *)
(* ------------------------------------------------------------------------- *)

let rec distrib fm =
  match fm with
    And(p,(Or(q,r))) -> Or(distrib(And(p,q)),distrib(And(p,r)))
  | And(Or(p,q),r) -> Or(distrib(And(p,r)),distrib(And(q,r)))
  | _ -> fm;;

let rec rawdnf fm =
  match fm with
    And(p,q) -> distrib(And(rawdnf p,rawdnf q))
  | Or(p,q) -> Or(rawdnf p,rawdnf q)
  | _ -> fm;;

let%expect_test "eg" =
  print_prop_formula
    (rawdnf {%prop|(p \/ q /\ r) /\ (~p \/ ~r)|});
  [%expect {| |}]
;;


(* ------------------------------------------------------------------------- *)
(* A version using a list representation.                                    *)
(* ------------------------------------------------------------------------- *)

let distrib s1 s2 = setify(allpairs union s1 s2);;

let rec purednf fm =
  match fm with
    And(p,q) -> distrib (purednf p) (purednf q)
  | Or(p,q) -> union (purednf p) (purednf q)
  | _ -> [[fm]];;

let%expect_test "eg" =
  print_prop_formula
    (purednf {%prop|(p \/ q /\ r) /\ (~p \/ ~r)|});
  [%expect {| |}]
;;


(* ------------------------------------------------------------------------- *)
(* Filtering out trivial disjuncts (in this guise, contradictory).           *)
(* ------------------------------------------------------------------------- *)

let trivial lits =
  let pos,neg = partition positive lits in
  intersect pos (image negate neg) <> [];;

let%expect_test "eg" =
  print_prop_formula
    (filter (non trivial) (purednf fm));
  [%expect {| |}]
;;


(* ------------------------------------------------------------------------- *)
(* With subsumption checking, done very naively (quadratic).                 *)
(* ------------------------------------------------------------------------- *)

let simpdnf fm =
  if fm = False then [] else if fm = True then [[]] else
  let djs = filter (non trivial) (purednf(nnf fm)) in
  filter (fun d -> not(exists (fun d' -> psubset d' d) djs)) djs;;

(* ------------------------------------------------------------------------- *)
(* Mapping back to a formula.                                                *)
(* ------------------------------------------------------------------------- *)

let dnf fm = list_disj(map list_conj (simpdnf fm));;

let%expect_test "eg" =
  let fm = {%prop|(p \/ q /\ r) /\ (~p \/ ~r)|} in
  print_prop_formula
    (fm);
  print_prop_formula
    (dnf fm);
  print_prop_formula
    (tautology(Iff(fm,dnf fm)));
  [%expect {| |}]
;;

(* ------------------------------------------------------------------------- *)
(* Conjunctive normal form (CNF) by essentially the same code.               *)
(* ------------------------------------------------------------------------- *)

let purecnf fm = image (image negate) (purednf(nnf(Not fm)));;

let simpcnf fm =
  if fm = False then [[]] else if fm = True then [] else
  let cjs = filter (non trivial) (purecnf fm) in
  filter (fun c -> not(exists (fun c' -> psubset c' c) cjs)) cjs;;

let cnf fm = list_conj(map list_disj (simpcnf fm));;

let%expect_test "eg" =
  let fm = {%prop|(p \/ q /\ r) /\ (~p \/ ~r)|} in
  print_prop_formula
    (fm);
  print_prop_formula
    (cnf fm);
  print_prop_formula
    (tautology(Iff(fm,cnf fm)));
  [%expect {| |}]
;;
