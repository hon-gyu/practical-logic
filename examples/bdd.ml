(* Interactive examples from bdd.ml, lifted out of the source by
   tools/migrate_to_modules.py.  Not compiled: these are meant to be
   pasted into a toplevel that has opened Atp.All. *)

bddtaut (mk_adder_test 4 2);;

(* ---- *)

ebddtaut (prime 101);;

ebddtaut (mk_adder_test 9 5);;
