(* Interactive examples from fol.ml, lifted out of the source by
   tools/migrate_to_modules.py.  Not compiled: these are meant to be
   pasted into a toplevel that has opened Atp.All. *)

Fn("sqrt",[Fn("-",[Fn("1",[]);
                   Fn("cos",[Fn("power",[Fn("+",[Var "x"; Var "y"]);
                                        Fn("2",[])])])])]);;

(* ---- *)

Atom(R("<",[Fn("+",[Var "x"; Var "y"]); Var "z"]));;

(* ---- *)

{%fol|(forall x. x < 2 ==> 2 * x <= 3) \/ false|};;

{%tm|2 * x|};;

(* ---- *)

{%fol|forall x y. exists z. x < z /\ y < z|};;

{%fol|~(forall x. P(x)) <=> exists y. ~P(y)|};;

(* ---- *)

holds bool_interp undefined {%fol|forall x. (x = 0) \/ (x = 1)|};;

holds (mod_interp 2) undefined {%fol|forall x. (x = 0) \/ (x = 1)|};;

holds (mod_interp 3) undefined {%fol|forall x. (x = 0) \/ (x = 1)|};;

let fm = {%fol|forall x. ~(x = 0) ==> exists y. x * y = 1|};;

filter (fun n -> holds (mod_interp n) undefined fm) (1--45);;

holds (mod_interp 3) undefined {%fol|(forall x. x = 0) ==> 1 = 0|};;
holds (mod_interp 3) undefined {%fol|forall x. x = 0 ==> 1 = 0|};;

(* ---- *)

variant "x" ["y"; "z"];;

variant "x" ["x"; "y"];;

variant "x" ["x"; "x'"];;

(* ---- *)

subst ("y" |=> Var "x") {%fol|forall x. x = y|};;

subst ("y" |=> Var "x") {%fol|forall x x'. x = y ==> x = x'|};;
