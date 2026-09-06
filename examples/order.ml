(* Interactive examples from order.ml, lifted out of the source by
   tools/migrate_to_modules.py.  Not compiled: these are meant to be
   pasted into a toplevel that has opened Atp.All. *)

let s = {%tm|f(x,x,x)|} and t = {%tm|g(x,y)|};;

termsize s > termsize t;;

let i = ("y" |=> {%tm|f(x,x,x)|});;

termsize (tsubst i s) > termsize (tsubst i t);;
