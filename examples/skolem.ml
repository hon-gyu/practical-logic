(* Interactive examples from skolem.ml, lifted out of the source.  Not compiled: these are meant to be
   pasted into a toplevel that has opened Atp.All. *)

simplify {%fol|(forall x y. P(x) \/ (P(y) /\ false)) ==> exists z. Q|};;

(* ---- *)

nnf {%fol|(forall x. P(x))
      ==> ((exists y. Q(y)) <=> exists z. P(z) /\ Q(z))|};;

(* ---- *)

pnf {%fol|(forall x. P(x) \/ R(y))
      ==> exists y z. Q(y) \/ ~(exists z. P(z) /\ Q(z))|};;

(* ---- *)

skolemize {%fol|exists y. x < y ==> forall u. exists v. x * u < y * v|};;

skolemize
 {%fol|forall x. P(x)
             ==> (exists y z. Q(y) \/ ~(exists z. P(z) /\ Q(z)))|};;
