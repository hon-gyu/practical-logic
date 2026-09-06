(* Interactive examples from defcnf.ml, lifted out of the source by
   tools/migrate_to_modules.py.  Not compiled: these are meant to be
   pasted into a toplevel that has opened Atp.All. *)

cnf {%prop|p <=> (q <=> r)|};;

(* ---- *)

defcnf {%prop|(p \/ (q /\ ~r)) /\ s|};;

(* ---- *)

defcnf {%prop|(p \/ (q /\ ~r)) /\ s|};;
