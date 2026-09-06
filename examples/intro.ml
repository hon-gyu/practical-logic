(* Interactive examples from intro.ml, lifted out of the source by
   tools/migrate_to_modules.py.  Not compiled: these are meant to be
   pasted into a toplevel that has opened Atp.All. *)

Add(Mul(Const 2,Var "x"),Var "y");;

(* ---- *)

let e = Add(Mul(Add(Mul(Const(0),Var "x"),Const(1)),Const(3)),
            Const(12));;
simplify e;;

(* ---- *)

lex(explode "2*((var_1 + x') + 11)");;
lex(explode "if (*p1-- == *p2++) then f() else g()");;

(* ---- *)

parse_expr "x + 1";;

(* ------------------------------------------------------------------------- *)
(* Demonstrate automatic installation.                                       *)
(* ------------------------------------------------------------------------- *)

{%expr|(x1 + x2 + x3) * (1 + 2 + 3 * x + y)|};;

(* ---- *)

string_of_exp {%expr|x + 3 * y|};;

(* ---- *)

{%expr|x + 3 * y|};;
{%expr|(x + 3) * y|};;
{%expr|1 + 2 + 3|};;
{%expr|((1 + 2) + 3) + 4|};;

(* ---- *)

{%expr|(x1 + x2 + x3 + x4 + x5 + x6 + x7 + x8 + x9 + x10) *
  (y1 + y2 + y3 + y4 + y5 + y6 + y7 + y8 + y9 + y10)|};;
