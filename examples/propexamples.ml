(* Interactive examples from propexamples.ml, lifted out of the source by
   tools/migrate_to_modules.py.  Not compiled: these are meant to be
   pasted into a toplevel that has opened Atp.All. *)

ramsey 3 3 4;;

tautology(ramsey 3 3 5);;

tautology(ramsey 3 3 6);;

(* ---- *)

let [x; y; out; c] = map mk_index ["X"; "Y"; "OUT"; "C"];;

ripplecarry x y c out 2;;

(* ---- *)

tautology(prime 7);;
tautology(prime 9);;
tautology(prime 11);;
