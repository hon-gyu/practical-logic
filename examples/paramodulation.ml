(* Interactive examples from paramodulation.ml, lifted out of the source by
   tools/migrate_to_modules.py.  Not compiled: these are meant to be
   pasted into a toplevel that has opened Atp.All. *)

paramodulation
 {%fol|(forall x. f(f(x)) = f(x)) /\ (forall x. exists y. f(y) = x)
   ==> forall x. f(x) = x|};;
