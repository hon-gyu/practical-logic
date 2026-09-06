(* Interactive examples from tableaux.ml, lifted out of the source by
   tools/migrate_to_modules.py.  Not compiled: these are meant to be
   pasted into a toplevel that has opened Atp.All. *)

let p20 = prawitz
 {%fol|(forall x y. exists z. forall w. P(x) /\ Q(y) ==> R(z) /\ U(w))
   ==> (exists x y. P(x) /\ Q(y)) ==> (exists z. R(z))|};;

(* ---- *)

let p19 = compare
 {%fol|exists x. forall y z. (P(y) ==> Q(z)) ==> P(x) ==> Q(x)|};;

let p20 = compare
 {%fol|(forall x y. exists z. forall w. P(x) /\ Q(y) ==> R(z) /\ U(w))
   ==> (exists x y. P(x) /\ Q(y)) ==> (exists z. R(z))|};;

let p24 = compare
 {%fol|~(exists x. U(x) /\ Q(x)) /\
   (forall x. P(x) ==> Q(x) \/ R(x)) /\
   ~(exists x. P(x) ==> (exists x. Q(x))) /\
   (forall x. Q(x) /\ R(x) ==> U(x))
   ==> (exists x. P(x) /\ R(x))|};;

let p39 = compare
 {%fol|~(exists x. forall y. P(y,x) <=> ~P(y,y))|};;

let p42 = compare
 {%fol|~(exists y. forall x. P(x,y) <=> ~(exists z. P(x,z) /\ P(z,x)))|};;

(***** Too slow?

let p43 = compare
 {%fol|(forall x y. Q(x,y) <=> forall z. P(z,x) <=> P(z,y))
   ==> forall x y. Q(x,y) <=> Q(y,x)|};;

 ******)

let p44 = compare
 {%fol|(forall x. P(x) ==> (exists y. G(y) /\ H(x,y)) /\
   (exists y. G(y) /\ ~H(x,y))) /\
   (exists x. J(x) /\ (forall y. G(y) ==> H(x,y)))
   ==> (exists x. J(x) /\ ~P(x))|};;

let p59 = compare
 {%fol|(forall x. P(x) <=> ~P(f(x))) ==> (exists x. P(x) /\ ~P(f(x)))|};;

let p60 = compare
 {%fol|forall x. P(x,f(x)) <=>
             exists y. (forall z. P(z,y) ==> P(z,f(x))) /\ P(x,y)|};;

(* ---- *)

let p38 = tab
 {%fol|(forall x.
     P(a) /\ (P(x) ==> (exists y. P(y) /\ R(x,y))) ==>
     (exists z w. P(z) /\ R(x,w) /\ R(w,z))) <=>
   (forall x.
     (~P(a) \/ P(x) \/ (exists z w. P(z) /\ R(x,w) /\ R(w,z))) /\
     (~P(a) \/ ~(exists y. P(y) /\ R(x,y)) \/
     (exists z w. P(z) /\ R(x,w) /\ R(w,z))))|};;

(* ---- *)

let p34 = splittab
 {%fol|((exists x. forall y. P(x) <=> P(y)) <=>
    ((exists x. Q(x)) <=> (forall y. Q(y)))) <=>
   ((exists x. forall y. Q(x) <=> Q(y)) <=>
    ((exists x. P(x)) <=> (forall y. P(y))))|};;

(* ------------------------------------------------------------------------- *)
(* Another nice example from EWD 1602.                                       *)
(* ------------------------------------------------------------------------- *)

let ewd1062 = splittab
 {%fol|(forall x. x <= x) /\
   (forall x y z. x <= y /\ y <= z ==> x <= z) /\
   (forall x y. f(x) <= y <=> x <= g(y))
   ==> (forall x y. x <= y ==> f(x) <= f(y)) /\
       (forall x y. x <= y ==> g(x) <= g(y))|};;
