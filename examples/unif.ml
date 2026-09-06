(* Interactive examples from unif.ml, lifted out of the source by
   tools/migrate_to_modules.py.  Not compiled: these are meant to be
   pasted into a toplevel that has opened Atp.All. *)

unify_and_apply [{%tm|f(x,g(y))|},{%tm|f(f(z),w)|}];;

unify_and_apply [{%tm|f(x,y)|},{%tm|f(y,x)|}];;

(****  unify_and_apply [{%tm|f(x,g(y))|},{%tm|f(y,x)|}];; *****)

unify_and_apply [{%tm|x_0|},{%tm|f(x_1,x_1)|};
                 {%tm|x_1|},{%tm|f(x_2,x_2)|};
                 {%tm|x_2|},{%tm|f(x_3,x_3)|}];;

let cyclic() = "cyclic" |=> parse_term "0";;

fullunify [parse_term "x", parse_term "x"];;

fullunify [parse_term "p(X,Y)", parse_term "p(Y,X)"];;

(* Makes solve do some work. *)
fullunify [parse_term "p(x,x)", parse_term "p(y,0)"];;

try fullunify [parse_term "p(x,x)", parse_term "p(y,f(y))"]
with Failure _ ->  cyclic();;

fullunify [parse_term "p(X,Y,2)", parse_term "p(Y,X,X)"];;

try fullunify [parse_term "Q(a, x, f(x))", parse_term "Q(2, y, y)"]
with Failure _ -> cyclic();;

fullunify [parse_term "Q(x, y, z)", parse_term "Q(u, h(v, v), u)"];;

fullunify [parse_term "q(p(X,Y),p(Y,X))", parse_term "q(Z,Z)"];;

(* This one gives "solve" some work to do. *)
let expander = [
  (parse_term "x"),(parse_term "f(y,y)");
  (parse_term "y"),(parse_term "f(z,z)");
  (parse_term "z"),(parse_term "f(w,w)")];;

unify undefined expander;;

fullunify expander;;
