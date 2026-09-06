(* Interactive examples from decidable.ml, lifted out of the source.  Not compiled: these are meant to be
   pasted into a toplevel that has opened Atp.All. *)

let los =
 {%fol|(forall x y z. P(x,y) /\ P(y,z) ==> P(x,z)) /\
   (forall x y z. Q(x,y) /\ Q(y,z) ==> Q(x,z)) /\
   (forall x y. P(x,y) ==> P(y,x)) /\
   (forall x y. P(x,y) \/ Q(x,y))
   ==> (forall x y. P(x,y)) \/ (forall x y. Q(x,y))|};;
skolemize(Not los);;

(* ------------------------------------------------------------------------- *)
(* The old DP procedure works.                                               *)
(* ------------------------------------------------------------------------- *)

davisputnam los;;

(* ---- *)

aedecide los;;

(* ---- *)

let fm = {%fol|(forall x. p(x)) \/ (exists y. p(y))|};;

pnf fm;;

(* ------------------------------------------------------------------------- *)
(* Also the group theory problem.                                            *)
(* ------------------------------------------------------------------------- *)

aedecide
 {%fol|(forall x. P(1,x,x)) /\ (forall x. P(x,x,1)) /\
   (forall u v w x y z.
        P(x,y,u) /\ P(y,z,w) ==> (P(x,w,v) <=> P(u,z,v)))
   ==> forall a b c. P(a,b,c) ==> P(b,a,c)|};;

aedecide
 {%fol|(forall x. P(x,x,1)) /\
   (forall u v w x y z.
        P(x,y,u) /\ P(y,z,w) ==> (P(x,w,v) <=> P(u,z,v)))
   ==> forall a b c. P(a,b,c) ==> P(b,a,c)|};;

(* ------------------------------------------------------------------------- *)
(* A bigger example.                                                         *)
(* ------------------------------------------------------------------------- *)

aedecide
 {%fol|(exists x. P(x)) /\ (exists x. G(x))
   ==> ((forall x. P(x) ==> H(x)) /\ (forall x. G(x) ==> J(x)) <=>
        (forall x y. P(x) /\ G(y) ==> H(x) /\ J(y)))|};;

(* ---- *)

miniscope(nnf {%fol|exists y. forall x. P(y) ==> P(x)|});;

let fm = miniscope(nnf
 {%fol|(forall x y. exists z. forall w. P(x) /\ Q(y) ==> R(z) /\ U(w))
   ==> (exists x y. P(x) /\ Q(y)) ==> (exists z. R(z))|});;

pnf(nnf fm);;

(* ---- *)

wang
 {%fol|(forall x y. exists z. forall w. P(x) /\ Q(y) ==> R(z) /\ U(w))
   ==> (exists x y. P(x) /\ Q(y)) ==> (exists z. R(z))|};;

(* ------------------------------------------------------------------------- *)
(* But not on this one!                                                      *)
(* ------------------------------------------------------------------------- *)

pnf(nnf(miniscope(nnf
 {%fol|((exists x. forall y. P(x) <=> P(y)) <=>
    ((exists x. Q(x)) <=> (forall y. Q(y)))) <=>
   ((exists x. forall y. Q(x) <=> Q(y)) <=>
    ((exists x. P(x)) <=> (forall y. P(y))))|})));;

(* ---- *)

let all_valid_syllogisms = filter aedecide all_possible_syllogisms;;

length all_valid_syllogisms;;

map anglicize_syllogism all_valid_syllogisms;;

(* ---- *)

let all_valid_syllogisms' = filter aedecide all_possible_syllogisms';;

length all_valid_syllogisms';;

map (anglicize_syllogism ** consequent) all_valid_syllogisms';;

(* ---- *)

decide_fmp
 {%fol|(forall x y. R(x,y) \/ R(y,x)) ==> forall x. R(x,x)|};;

decide_fmp
 {%fol|(forall x y z. R(x,y) /\ R(y,z) ==> R(x,z)) ==> forall x. R(x,x)|};;

(*** This fails to terminate: has countermodels, but only infinite ones
decide_fmp
 {%fol|~((forall x. ~R(x,x)) /\
     (forall x. exists z. R(x,z)) /\
     (forall x y z. R(x,y) /\ R(y,z) ==> R(x,z)))|};;
****)

(* ---- *)

decide_monadic
 {%fol|((exists x. forall y. P(x) <=> P(y)) <=>
    ((exists x. Q(x)) <=> (forall y. Q(y)))) <=>
    ((exists x. forall y. Q(x) <=> Q(y)) <=>
   ((exists x. P(x)) <=> (forall y. P(y))))|};;

(**** This is not feasible
decide_monadic
 {%fol|(forall x y. exists z. forall w. P(x) /\ Q(y) ==> R(z) /\ U(w))
   ==> (exists x y. P(x) /\ Q(y)) ==> (exists z. R(z))|};;
 ****)

(* ---- *)

(*** Our claimed equivalences are indeed correct ***)

meson
 {%fol|(exists x y z. forall u.
        R(x,x) \/ ~R(x,u) \/ (R(x,y) /\ R(y,z) /\ ~R(x,z))) <=>
   ~((forall x. ~R(x,x)) /\
     (forall x. exists z. R(x,z)) /\
     (forall x y z. R(x,y) /\ R(y,z) ==> R(x,z)))|};;

meson
 {%fol|(exists x. forall y. exists z. R(x,x) \/ ~R(x,y) \/ (R(y,z) /\ ~R(x,z))) <=>
   ~((forall x. ~R(x,x)) /\
     (forall x. exists y. R(x,y) /\ forall z. R(y,z) ==> R(x,z)))|};;

(*** The second formula implies the first ***)

meson
{%fol|~((forall x. ~R(x,x)) /\
    (forall x. exists y. R(x,y) /\ forall z. R(y,z) ==> R(x,z)))
  ==> ~((forall x. ~R(x,x)) /\
        (forall x. exists z. R(x,z)) /\
        (forall x y z. R(x,y) /\ R(y,z) ==> R(x,z)))|};;
