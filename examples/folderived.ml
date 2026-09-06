(* Interactive examples from folderived.ml, lifted out of the source by
   tools/migrate_to_modules.py.  Not compiled: these are meant to be
   pasted into a toplevel that has opened Atp.All. *)

icongruence {%tm|s|} {%tm|t|} {%tm|f(s,g(s,t,s),u,h(h(s)))|}
                            {%tm|f(s,g(t,t,s),u,h(h(t)))|};;

(* ---- *)

ispec {%tm|y|} {%fol|forall x y z. x + y + z = z + y + x|};;

(* ------------------------------------------------------------------------- *)
(* Additional tests not in main text.                                        *)
(* ------------------------------------------------------------------------- *)

isubst {%tm|x + x|} {%tm|2 * x|}
        {%fol|x + x = x ==> x = 0|} {%fol|2 * x = x ==> x = 0|};;

isubst {%tm|x + x|}  {%tm|2 * x|}
       {%fol|(x + x = y + y) ==> (y + y + y = x + x + x)|}
       {%fol|2 * x = y + y ==> y + y + y = x + 2 * x|};;

ispec {%tm|x|} {%fol|forall x y z. x + y + z = y + z + z|} ;;

ispec {%tm|x|} {%fol|forall x. x = x|} ;;

ispec {%tm|w + y + z|} {%fol|forall x y z. x + y + z = y + z + z|} ;;

ispec {%tm|x + y + z|} {%fol|forall x y z. x + y + z = y + z + z|} ;;

ispec {%tm|x + y + z|} {%fol|forall x y z. nothing_much|} ;;

isubst {%tm|x + x|} {%tm|2 * x|}
       {%fol|(x + x = y + y) <=> (something \/ y + y + y = x + x + x)|} ;;

isubst {%tm|x + x|}  {%tm|2 * x|}
       {%fol|(exists x. x = 2) <=> exists y. y + x + x = y + y + y|}
       {%fol|(exists x. x = 2) <=> (exists y. y + 2 * x = y + y + y)|};;

isubst {%tm|x|}  {%tm|y|}
        {%fol|(forall z. x = z) <=> (exists x. y < z) /\ (forall y. y < x)|}
        {%fol|(forall z. y = z) <=> (exists x. y < z) /\ (forall y'. y' < y)|};;

(* ------------------------------------------------------------------------- *)
(* The bug is now fixed.                                                     *)
(* ------------------------------------------------------------------------- *)

ispec {%tm|x'|} {%fol|forall x x' x''. x + x' + x'' = 0|};;

ispec {%tm|x''|} {%fol|forall x x' x''. x + x' + x'' = 0|};;

ispec {%tm|x' + x''|} {%fol|forall x x' x''. x + x' + x'' = 0|};;

ispec {%tm|x + x' + x''|} {%fol|forall x x' x''. x + x' + x'' = 0|};;

ispec {%tm|2 * x|} {%fol|forall x x'. x + x' = x' + x|};;
