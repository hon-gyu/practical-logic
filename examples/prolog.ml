(* Interactive examples from prolog.ml, lifted out of the source.  Not compiled: these are meant to be
   pasted into a toplevel that has opened Atp.All. *)

let p32 = hornprove
 {%fol|(forall x. P(x) /\ (G(x) \/ H(x)) ==> Q(x)) /\
   (forall x. Q(x) /\ H(x) ==> J(x)) /\
   (forall x. R(x) ==> H(x))
   ==> (forall x. P(x) /\ R(x) ==> J(x))|};;

(* ------------------------------------------------------------------------- *)
(* A non-Horn example.                                                       *)
(* ------------------------------------------------------------------------- *)

(****************

hornprove {%fol|(p \/ q) /\ (~p \/ q) /\ (p \/ ~q) ==> ~(~q \/ ~q)|};;

**********)

(* ---- *)

let lerules = ["0 <= X"; "S(X) <= S(Y) :- X <= Y"];;

simpleprolog lerules "S(S(0)) <= S(S(S(0)))";;

(*** simpleprolog lerules "S(S(0)) <= S(0)";;
 ***)

let env = simpleprolog lerules "S(S(0)) <= X";;
apply env "X";;

(* ---- *)

prolog lerules "S(S(0)) <= X";;

(* ------------------------------------------------------------------------- *)
(* Append example, showing symmetry between inputs and outputs.              *)
(* ------------------------------------------------------------------------- *)

let appendrules =
  ["append(nil,L,L)"; "append(H::T,L,H::A) :- append(T,L,A)"];;

prolog appendrules "append(1::2::nil,3::4::nil,Z)";;

prolog appendrules "append(1::2::nil,Y,1::2::3::4::nil)";;

prolog appendrules "append(X,3::4::nil,1::2::3::4::nil)";;

prolog appendrules "append(X,Y,1::2::3::4::nil)";;

(* ------------------------------------------------------------------------- *)
(* However this way round doesn't work.                                      *)
(* ------------------------------------------------------------------------- *)

(***
 *** prolog appendrules "append(X,3::4::nil,X)";;
 ***)

(* ------------------------------------------------------------------------- *)
(* A sorting example (from Lloyd's "Foundations of Logic Programming").      *)
(* ------------------------------------------------------------------------- *)

let sortrules =
 ["sort(X,Y) :- perm(X,Y),sorted(Y)";
  "sorted(nil)";
  "sorted(X::nil)";
  "sorted(X::Y::Z) :- X <= Y, sorted(Y::Z)";
  "perm(nil,nil)";
  "perm(X::Y,U::V) :- delete(U,X::Y,Z), perm(Z,V)";
  "delete(X,X::Y,Y)";
  "delete(X,Y::Z,Y::W) :- delete(X,Z,W)";
  "0 <= X";
  "S(X) <= S(Y) :- X <= Y"];;

prolog sortrules
  "sort(S(S(S(S(0))))::S(0)::0::S(S(0))::S(0)::nil,X)";;

(* ------------------------------------------------------------------------- *)
(* Yet with a simple swap of the first two predicates...                     *)
(* ------------------------------------------------------------------------- *)

let badrules =
 ["sort(X,Y) :- sorted(Y), perm(X,Y)";
  "sorted(nil)";
  "sorted(X::nil)";
  "sorted(X::Y::Z) :- X <= Y, sorted(Y::Z)";
  "perm(nil,nil)";
  "perm(X::Y,U::V) :- delete(U,X::Y,Z), perm(Z,V)";
  "delete(X,X::Y,Y)";
  "delete(X,Y::Z,Y::W) :- delete(X,Z,W)";
  "0 <= X";
  "S(X) <= S(Y) :- X <= Y"];;

(*** This no longer works

prolog badrules
  "sort(S(S(S(S(0))))::S(0)::0::S(S(0))::S(0)::nil,X)";;

 ***)
