(* Interactive examples from stal.ml, lifted out of the source.  Not compiled: these are meant to be
   pasted into a toplevel that has opened Atp.All. *)

triggers {%prop|p <=> (q /\ r)|};;

(* ---- *)

time stalmarck (mk_adder_test 6 3);;
