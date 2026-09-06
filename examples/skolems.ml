(* Interactive examples from skolems.ml, lifted out of the source.  Not compiled: these are meant to be
   pasted into a toplevel that has opened Atp.All. *)

skolemizes [{%fol|exists x y. x + y = 2|};
            {%fol|forall x. exists y. x + 1 = y|}];;
