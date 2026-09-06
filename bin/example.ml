(* ========================================================================= *)
(* Some examples illustrating how the theorem-proving code can be used.      *)
(*                                                                           *)
(* Copyright (c) 2003-2007, John Harrison. (See "LICENSE.txt" for details.)  *)
(* ========================================================================= *)

open Atp.All

let () = Atp.Initialization.init ();;

print_string "Starting examples\n";;

(* ------------------------------------------------------------------------- *)
(* Printer for formulas, to give feedback when not using toplevel.           *)
(* ------------------------------------------------------------------------- *)

let print_formula fm = print_qformula print_atom fm; print_newline();;

(* ------------------------------------------------------------------------- *)
(* Prove Dijkstra's "Golden Rule" via naive tautology algorithm.             *)
(* ------------------------------------------------------------------------- *)

let gold = {%fol|p /\ q <=> ((p <=> q) <=> p \/ q)|} in
if tautology gold then print_formula gold else failwith "Not a tautology";;

(* ------------------------------------------------------------------------- *)
(* Solve some instances of Urquhart problems using Stalmarck's algorithm.    *)
(* ------------------------------------------------------------------------- *)

let urquhart n =
  let pvs = map (fun n -> Atom(P("p_"^(string_of_int n)))) (1 -- n) in
  end_itlist (fun p q -> Iff(p,q)) (pvs @ pvs);;

do_list (time stalmarck ** urquhart) [1;2;4;8;16];;

(* ------------------------------------------------------------------------- *)
(* Print a propositional formula asserting that 11 is a prime number.        *)
(* ------------------------------------------------------------------------- *)

let prf = prime 11 in
print_qformula print_propvar prf; print_newline();;

(* ------------------------------------------------------------------------- *)
(* Prove Agatha formula using simple tableaux after initial splitting.       *)
(* ------------------------------------------------------------------------- *)

let p55 =
 {%fol|lives(agatha) /\ lives(butler) /\ lives(charles) /\
   (killed(agatha,agatha) \/ killed(butler,agatha) \/
    killed(charles,agatha)) /\
   (forall x y. killed(x,y) ==> hates(x,y) /\ ~richer(x,y)) /\
   (forall x. hates(agatha,x) ==> ~hates(charles,x)) /\
   (hates(agatha,agatha) /\ hates(agatha,charles)) /\
   (forall x. lives(x) /\ ~richer(x,agatha) ==> hates(butler,x)) /\
   (forall x. hates(agatha,x) ==> hates(butler,x)) /\
   (forall x. ~hates(x,agatha) \/ ~hates(x,butler) \/ ~hates(x,charles))
   ==> killed(agatha,agatha) /\
       ~killed(butler,agatha) /\
       ~killed(charles,agatha)|} in
if can (time splittab) p55 then print_formula p55
else failwith "Proof failed";;

(* ------------------------------------------------------------------------- *)
(* Prove the Los formula using positive resolution.                          *)
(* ------------------------------------------------------------------------- *)

let los =
 {%fol|(forall x y z. P(x,y) ==> P(y,z) ==> P(x,z)) /\
   (forall x y z. Q(x,y) ==> Q(y,z) ==> Q(x,z)) /\
   (forall x y. Q(x,y) ==> Q(y,x)) /\
   (forall x y. P(x,y) \/ Q(x,y))
   ==> (forall x y. P(x,y)) \/ (forall x y. Q(x,y))|} in
 if can (time presolution) los then print_formula los
 else failwith "Proof failed";;

(* ------------------------------------------------------------------------- *)
(* Prove Wishnu Prasetya's formula by just adding equality axioms.           *)
(* ------------------------------------------------------------------------- *)

let wishnu =
 {%fol|(exists x. x = f(g(x)) /\ forall x'. x' = f(g(x')) ==> x = x') <=>
   (exists y. y = g(f(y)) /\ forall y'. y' = g(f(y')) ==> y = y')|} in
 if can meson (equalitize wishnu) then print_formula wishnu
 else failwith "Formula was not proved";;

(* ------------------------------------------------------------------------- *)
(* Prove a formula from EWD1266a using paramodulation.                       *)
(* ------------------------------------------------------------------------- *)

let ewd =
 {%fol|(forall x. f(x) ==> g(x)) /\
   (exists x. f(x)) /\
   (forall x y. g(x) /\ g(y) ==> x = y)
   ==> forall y. g(y) ==> f(y)|} in
if can (time paramodulation) ewd then print_formula ewd
else failwith "Proof failed";;

(* ------------------------------------------------------------------------- *)
(* Perform Knuth-Bendix completion on the group axioms.                      *)
(* ------------------------------------------------------------------------- *)

let eqs =
  complete_and_simplify
    ["1"; "*"; "i"]
    [{%fol|1 * x = x|}; {%fol|i(x) * x = 1|}; {%fol|(x * y) * z = x * y * z|}] in
  do_list print_formula eqs;;

(* ------------------------------------------------------------------------- *)
(* Produce all valid syllogisms (permitting empty relations).                *)
(* ------------------------------------------------------------------------- *)

let all_valid_syllogisms =
  map anglicize_syllogism (filter aedecide all_possible_syllogisms) in
do_list (fun syl -> print_string syl; print_newline()) all_valid_syllogisms;;

(* ------------------------------------------------------------------------- *)
(* Check a resultant (from Maple) by complex quantifier elimination.         *)
(* ------------------------------------------------------------------------- *)

let result =
  time complex_qelim
   {%fol|forall a b c d e f.
       (exists x. a * x^2 + b * x + c = 0 /\ d * x^2 + e * x + f = 0) \/
       (a = 0) /\ (d = 0) <=>
       d^2*c^2-2*d*c*a*f+a^2*f^2-e*d*b*c-e*b*a*f+a*e^2*c+f*d*b^2 = 0|} in
print_formula result;;

(* ------------------------------------------------------------------------- *)
(* Perform real quantifier elimination on false and true quadratic criteria. *)
(* ------------------------------------------------------------------------- *)

let quad_f =
  time real_qelim
   {%fol|forall a b c. (exists x. a * x^2 + b * x + c = 0) <=>
                   b^2 >= 4 * a * c|} in
print_formula quad_f;;

let quad_t =
  time real_qelim
   {%fol|forall a b c. (exists x. a * x^2 + b * x + c = 0) <=>
                   a = 0 /\ (~(b = 0) \/ c = 0) \/
                   ~(a = 0) /\ b^2 >= 4 * a * c|} in
print_formula quad_t;;

(* ------------------------------------------------------------------------- *)
(* Prove a key lemma for Loeb's theorem by Mizar-like interactive proof and  *)
(* turn it into a strict LCF proof afterwards.                               *)
(* ------------------------------------------------------------------------- *)

let lob = prove
 {%fol|(forall p. |--(p) ==> |--(Pr(p))) /\
   (forall p q. |--(imp(Pr(imp(p,q)),imp(Pr(p),Pr(q))))) /\
   (forall p. |--(imp(Pr(p),Pr(Pr(p)))))
   ==> (forall p q. |--(imp(p,q)) /\ |--(p) ==> |--(q)) /\
       (forall p q. |--(imp(q,imp(p,q)))) /\
       (forall p q r. |--(imp(imp(p,imp(q,r)),imp(imp(p,q),imp(p,r)))))
       ==> |--(imp(G,imp(Pr(G),S))) /\ |--(imp(imp(Pr(G),S),G))
           ==> |--(imp(Pr(S),S)) ==> |--(S)|}
 [assume["lob1",{%fol|forall p. |--(p) ==> |--(Pr(p))|};                           
         "lob2",{%fol|forall p q. |--(imp(Pr(imp(p,q)),imp(Pr(p),Pr(q))))|};       
         "lob3",{%fol|forall p. |--(imp(Pr(p),Pr(Pr(p))))|}];                      
  assume["logic",{%fol|(forall p q. |--(imp(p,q)) /\ |--(p) ==> |--(q)) /\         
                   (forall p q. |--(imp(q,imp(p,q)))) /\               
                   (forall p q r. |--(imp(imp(p,imp(q,r)),             
                                      imp(imp(p,q),imp(p,r)))))|}];            
  assume ["fix1",{%fol||--(imp(G,imp(Pr(G),S)))|};                                 
          "fix2",{%fol||--(imp(imp(Pr(G),S),G))|}];                                
  assume["consistency",{%fol||--(imp(Pr(S),S))|}];                                 
  have {%fol||--(Pr(imp(G,imp(Pr(G),S))))|} by ["lob1"; "fix1"];                   
  so have {%fol||--(imp(Pr(G),Pr(imp(Pr(G),S))))|} by ["lob2"; "logic"];           
  so have {%fol||--(imp(Pr(G),imp(Pr(Pr(G)),Pr(S))))|} by ["lob2"; "logic"];       
  so have {%fol||--(imp(Pr(G),Pr(S)))|} by ["lob3"; "logic"];
  so note("L",{%fol||--(imp(Pr(G),S))|}) by ["consistency"; "logic"];
  so have {%fol||--(G)|} by ["fix2"; "logic"];
  so have {%fol||--(Pr(G))|} by ["lob1"; "logic"];
  so conclude {%fol||--(S)|} by ["L"; "logic"];
  qed] in
  print_thm lob; print_newline();;
