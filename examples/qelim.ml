(* Interactive examples from qelim.ml, lifted out of the source by
   tools/migrate_to_modules.py.  Not compiled: these are meant to be
   pasted into a toplevel that has opened Atp.All. *)

quelim_dlo {%fol|forall x y. exists z. z < x /\ z < y|};;

quelim_dlo {%fol|exists z. z < x /\ z < y|};;

quelim_dlo {%fol|exists z. x < z /\ z < y|};;

quelim_dlo {%fol|(forall x. x < a ==> x < b)|};;

quelim_dlo {%fol|forall a b. (forall x. x < a ==> x < b) <=> a <= b|};;

quelim_dlo {%fol|forall a b. (forall x. x < a <=> x < b) <=> a = b|};;

quelim_dlo {%fol|exists x y z. forall u.
                 x < x \/ ~x < u \/ (x < y /\ y < z /\ ~x < z)|};;

(* ------------------------------------------------------------------------- *)
(* More tests (not in the text).                                             *)
(* ------------------------------------------------------------------------- *)

time quelim_dlo {%fol|forall x. exists y. x < y|};;

time quelim_dlo {%fol|forall x y z. x < y /\ y < z ==> x < z|};;

time quelim_dlo {%fol|forall x y. x < y \/ (x = y) \/ y < x|};;

time quelim_dlo {%fol|exists x y. x < y /\ y < x|};;

time quelim_dlo {%fol|forall x y. exists z. z < x /\ x < y|};;

time quelim_dlo {%fol|exists z. z < x /\ x < y|};;

time quelim_dlo {%fol|forall x y. exists z. z < x /\ z < y|};;

time quelim_dlo {%fol|forall x y. x < y ==> exists z. x < z /\ z < y|};;

time quelim_dlo
  {%fol|forall x y. ~(x = y) ==> exists u. u < x /\ (y < u \/ x < y)|};;

time quelim_dlo {%fol|exists x. x = x|};;

time quelim_dlo {%fol|exists x. x = x /\ x = y|};;

time quelim_dlo {%fol|exists z. x < z /\ z < y|};;

time quelim_dlo {%fol|exists z. x <= z /\ z <= y|};;

time quelim_dlo {%fol|exists z. x < z /\ z <= y|};;

time quelim_dlo {%fol|forall x y z. exists u. u < x /\ u < y /\ u < z|};;

time quelim_dlo {%fol|forall y. x < y /\ y < z ==> w < z|};;

time quelim_dlo {%fol|forall x y. x < y|};;

time quelim_dlo {%fol|exists z. z < x /\ x < y|};;

time quelim_dlo {%fol|forall a b. (forall x. x < a ==> x < b) <=> a <= b|};;

time quelim_dlo {%fol|forall x. x < a ==> x < b|};;

time quelim_dlo {%fol|forall x. x < a ==> x <= b|};;

time quelim_dlo {%fol|forall a b. exists x. ~(x = a) \/ ~(x = b) \/ (a = b)|};;

time quelim_dlo {%fol|forall x y. x <= y \/ x > y|};;

time quelim_dlo {%fol|forall x y. x <= y \/ x < y|};;
