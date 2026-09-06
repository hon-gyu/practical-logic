(* Interactive examples from prop.ml, lifted out of the source.  Not compiled: these are meant to be
   pasted into a toplevel that has opened Atp.All. *)

let fm = {%prop|p ==> q <=> r /\ s \/ (t <=> ~ ~u /\ v)|};;

And(fm,fm);;

And(Or(fm,fm),fm);;

(* ---- *)

eval {%prop|p /\ q ==> q /\ r|}
     (function P"p" -> true | P"q" -> false | P"r" -> true);;

eval {%prop|p /\ q ==> q /\ r|}
     (function P"p" -> true | P"q" -> true | P"r" -> false);;

(* ---- *)

atoms {%prop|p /\ q \/ s ==> ~p \/ (r <=> s)|};;

(* ---- *)

print_truthtable {%prop|p /\ q ==> q /\ r|};;

let fm = {%prop|p /\ q ==> q /\ r|};;

print_truthtable fm;;

(* ---- *)

print_truthtable {%prop|((p ==> q) ==> p) ==> p|};;

print_truthtable {%prop|p /\ ~p|};;

(* ---- *)

tautology {%prop|p \/ ~p|};;

tautology {%prop|p \/ q ==> p|};;

tautology {%prop|p \/ q ==> q \/ (p <=> q)|};;

tautology {%prop|(p \/ q) /\ ~(p /\ q) ==> (~p <=> q)|};;

(* ---- *)

psubst (P"p" |=> {%prop|p /\ q|}) {%prop|p /\ q /\ p /\ q|};;

(* ---- *)

tautology {%prop|(p ==> q) \/ (q ==> p)|};;

tautology {%prop|p \/ (q <=> r) <=> (p \/ q <=> p \/ r)|};;

tautology {%prop|p /\ q <=> ((p <=> q) <=> p \/ q)|};;

tautology {%prop|(p ==> q) <=> (~q ==> ~p)|};;

tautology {%prop|(p ==> ~q) <=> (q ==> ~p)|};;

tautology {%prop|(p ==> q) <=> (q ==> p)|};;

(* ------------------------------------------------------------------------- *)
(* Some logical equivalences allowing elimination of connectives.            *)
(* ------------------------------------------------------------------------- *)

forall tautology
 [{%prop|true <=> false ==> false|};
  {%prop|~p <=> p ==> false|};
  {%prop|p /\ q <=> (p ==> q ==> false) ==> false|};
  {%prop|p \/ q <=> (p ==> false) ==> q|};
  {%prop|(p <=> q) <=> ((p ==> q) ==> (q ==> p) ==> false) ==> false|}];;

(* ---- *)

dual {%prop|p \/ ~p|};;

(* ---- *)

psimplify {%prop|(true ==> (x <=> false)) ==> ~(y \/ false /\ z)|};;

psimplify {%prop|((x ==> y) ==> true) \/ ~false|};;

(* ---- *)

let fm = {%prop|(p <=> q) <=> ~(r ==> s)|};;

let fm' = nnf fm;;

tautology(Iff(fm,fm'));;

(* ---- *)

tautology {%prop|(p ==> p') /\ (q ==> q') ==> (p /\ q ==> p' /\ q')|};;
tautology {%prop|(p ==> p') /\ (q ==> q') ==> (p \/ q ==> p' \/ q')|};;

(* ---- *)

let fm = {%prop|(p \/ q /\ r) /\ (~p \/ ~r)|};;

dnf fm;;

print_truthtable fm;;

dnf {%prop|p /\ q /\ r /\ s /\ t /\ u \/ u /\ v|};;

(* ---- *)

rawdnf {%prop|(p \/ q /\ r) /\ (~p \/ ~r)|};;

(* ---- *)

purednf {%prop|(p \/ q /\ r) /\ (~p \/ ~r)|};;

(* ---- *)

filter (non trivial) (purednf fm);;

(* ---- *)

let fm = {%prop|(p \/ q /\ r) /\ (~p \/ ~r)|};;
dnf fm;;
tautology(Iff(fm,dnf fm));;

(* ---- *)

let fm = {%prop|(p \/ q /\ r) /\ (~p \/ ~r)|};;
cnf fm;;
tautology(Iff(fm,cnf fm));;
