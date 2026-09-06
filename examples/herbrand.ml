(* Interactive examples from herbrand.ml, lifted out of the source by
   tools/migrate_to_modules.py.  Not compiled: these are meant to be
   pasted into a toplevel that has opened Atp.All. *)

gilmore {%fol|exists x. forall y. P(x) ==> P(y)|};;

let sfm = skolemize(Not {%fol|exists x. forall y. P(x) ==> P(y)|});;

(* ------------------------------------------------------------------------- *)
(* Quick example.                                                            *)
(* ------------------------------------------------------------------------- *)

let p24 = gilmore
 {%fol|~(exists x. U(x) /\ Q(x)) /\
   (forall x. P(x) ==> Q(x) \/ R(x)) /\
   ~(exists x. P(x) ==> (exists x. Q(x))) /\
   (forall x. Q(x) /\ R(x) ==> U(x))
   ==> (exists x. P(x) /\ R(x))|};;

(* ------------------------------------------------------------------------- *)
(* Slightly less easy example.                                               *)
(* ------------------------------------------------------------------------- *)

let p45 = gilmore
 {%fol|(forall x. P(x) /\ (forall y. G(y) /\ H(x,y) ==> J(x,y))
              ==> (forall y. G(y) /\ H(x,y) ==> R(y))) /\
   ~(exists y. L(y) /\ R(y)) /\
   (exists x. P(x) /\ (forall y. H(x,y) ==> L(y)) /\
                      (forall y. G(y) /\ H(x,y) ==> J(x,y)))
   ==> (exists x. P(x) /\ ~(exists y. G(y) /\ H(x,y)))|};;

(* ---- *)

let p20 = davisputnam
 {%fol|(forall x y. exists z. forall w. P(x) /\ Q(y) ==> R(z) /\ U(w))
   ==> (exists x y. P(x) /\ Q(y)) ==> (exists z. R(z))|};;

(* ---- *)

let p36 = davisputnam'
 {%fol|(forall x. exists y. P(x,y)) /\
   (forall x. exists y. G(x,y)) /\
   (forall x y. P(x,y) \/ G(x,y)
                ==> (forall z. P(y,z) \/ G(y,z) ==> H(x,z)))
   ==> (forall x. exists y. H(x,y))|};;

let p29 = davisputnam'
 {%fol|(exists x. P(x)) /\ (exists x. G(x)) ==>
   ((forall x. P(x) ==> H(x)) /\ (forall x. G(x) ==> J(x)) <=>
    (forall x y. P(x) /\ G(y) ==> H(x) /\ J(y)))|};;
