(* Interactive examples from lcfprop.ml, lifted out of the source.  Not compiled: these are meant to be
   pasted into a toplevel that has opened Atp.All. *)

lcftaut {%fol|(p ==> q) \/ (q ==> p)|};;

lcftaut {%fol|p /\ q <=> ((p <=> q) <=> p \/ q)|};;

lcftaut {%fol|((p <=> q) <=> r) <=> (p <=> (q <=> r))|};;
