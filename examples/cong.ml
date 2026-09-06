(* Interactive examples from cong.ml, lifted out of the source by
   tools/migrate_to_modules.py.  Not compiled: these are meant to be
   pasted into a toplevel that has opened Atp.All. *)

ccvalid {%fol|f(f(f(f(f(c))))) = c /\ f(f(f(c))) = c
          ==> f(c) = c \/ f(g(c)) = g(f(c))|};;

ccvalid {%fol|f(f(f(f(c)))) = c /\ f(f(c)) = c ==> f(c) = c|};;

(* ------------------------------------------------------------------------- *)
(* For debugging. Maybe I will incorporate into a prettyprinter one day.     *)
(* ------------------------------------------------------------------------- *)

(**********

let showequiv ptn =
  let fn = reverseq (equated ptn) ptn in
  map (apply fn) (dom fn);;

 **********)
