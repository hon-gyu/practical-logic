(* Interactive examples from rewrite.ml, lifted out of the source by
   tools/migrate_to_modules.py.  Not compiled: these are meant to be
   pasted into a toplevel that has opened Atp.All. *)

rewrite [{%fol|0 + x = x|}; {%fol|S(x) + y = S(x + y)|};
         {%fol|0 * x = 0|}; {%fol|S(x) * y = y + x * y|}]
        {%tm|S(S(S(0))) * S(S(0)) + S(S(S(S(0))))|};;
