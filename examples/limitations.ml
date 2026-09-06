(* Interactive examples from limitations.ml, lifted out of the source by
   tools/migrate_to_modules.py.  Not compiled. *)

gform {%fol|~(x = 0)|};;

(* ---- *)

gform {%fol|x = x|};;
gform {%fol|0 < 0|};;

(* ---- *)

diag("p(x)");;
diag("This string is diag(x)");;

(* ---- *)

diag("The result of substituting the quotation of x for `x' in x \
        has property P");;

(* ---- *)

let prime_form p = subst("p" |=> numeral(Int p))
 {%fol|S(S(0)) <= p /\
   forall n. n < p ==> (exists x. x <= p /\ p = n * x) ==> n = S(0)|};;

dholds undefined (prime_form 100);;
dholds undefined (prime_form 101);;

(* ---- *)

classify Sigma 1
  {%fol|forall x. x < 2
              ==> exists y z. forall w. w < x + 2
                                        ==> w + x + y + z = 42|};;

(* ---- *)

sigma_bound
  {%fol|exists p x.
     p < x /\
     (S(S(0)) <= p /\
      forall n. n < p
                ==> (exists x. x <= p /\ p = n * x) ==> n = S(0)) /\
     ~(x = 0) /\
     forall z. z <= x
               ==> (exists w. w <= x /\ x = z * w)
                   ==> z = S(0) \/ exists x. x <= z /\ z = p * x|};;

(* ---- *)

let prog_suc = itlist (fun m -> m)
 [(1,Blank) |-> (Blank,Right,2);
  (2,One) |-> (One,Right,2);
  (2,Blank) |-> (One,Right,3);
  (3,Blank) |-> (Blank,Left,4);
  (3,One) |-> (Blank,Left,4);
  (4,One) |-> (One,Left,4);
  (4,Blank) |-> (Blank,Stay,0)]
 undefined;;

exec prog_suc [0];;

exec prog_suc [1];;

exec prog_suc [19];;

(* ---- *)

robeval {%tm|S(0) + (S(S(0)) * ((S(0) + S(S(0)) + S(0))))|};;

(* ---- *)

rob_ne {%tm|S(0) + S(0) + S(0)|} {%tm|S(S(0)) * S(S(0))|};;
rob_ne {%tm|0 + 0 * S(0)|} {%tm|S(S(0)) + 0|};;
rob_ne {%tm|S(S(0)) + 0|} {%tm|0 + 0 + 0 * 0|};;

(* ---- *)

sigma_prove
  {%fol|exists p.
      S(S(0)) <= p /\
      forall n. n < p
                ==> (exists x. x <= p /\ p = n * x) ==> n = S(0)|};;

(* ---- *)

meson
 {%fol|(True(G) <=> ~(|--(G))) /\ Pi(G) /\
   (forall p. Sigma(p) ==> (|--(p) <=> True(p))) /\
   (forall p. True(Not(p)) <=> ~True(p)) /\
   (forall p. Pi(p) ==> Sigma(Not(p)))
   ==> (|--(Not(G)) <=> |--(G))|};;

(* ---- *)

let godel_2 = prove
 {%fol|(forall p. |--(p) ==> |--(Pr(p))) /\
   (forall p q. |--(imp(Pr(imp(p,q)),imp(Pr(p),Pr(q))))) /\
   (forall p. |--(imp(Pr(p),Pr(Pr(p)))))
   ==> (forall p q. |--(imp(p,q)) /\ |--(p) ==> |--(q)) /\
       (forall p q. |--(imp(q,imp(p,q)))) /\
       (forall p q r. |--(imp(imp(p,imp(q,r)),imp(imp(p,q),imp(p,r)))))
       ==> |--(imp(G,imp(Pr(G),F))) /\ |--(imp(imp(Pr(G),F),G))
           ==> |--(imp(Pr(F),F)) ==> |--(F)|}
 [assume["lob1",{%fol|forall p. |--(p) ==> |--(Pr(p))|};
         "lob2",{%fol|forall p q. |--(imp(Pr(imp(p,q)),imp(Pr(p),Pr(q))))|};
         "lob3",{%fol|forall p. |--(imp(Pr(p),Pr(Pr(p))))|}];
  assume["logic",{%fol|(forall p q. |--(imp(p,q)) /\ |--(p) ==> |--(q)) /\
                   (forall p q. |--(imp(q,imp(p,q)))) /\
                   (forall p q r. |--(imp(imp(p,imp(q,r)),
                                      imp(imp(p,q),imp(p,r)))))|}];
  assume ["fix1",{%fol||--(imp(G,imp(Pr(G),F)))|};
          "fix2",{%fol||--(imp(imp(Pr(G),F),G))|}];
  assume["consistency",{%fol||--(imp(Pr(F),F))|}];
  have {%fol||--(Pr(imp(G,imp(Pr(G),F))))|} by ["lob1"; "fix1"];
  so have {%fol||--(imp(Pr(G),Pr(imp(Pr(G),F))))|} by ["lob2"; "logic"];
  so have {%fol||--(imp(Pr(G),imp(Pr(Pr(G)),Pr(F))))|} by ["lob2"; "logic"];
  so have {%fol||--(imp(Pr(G),Pr(F)))|} by ["lob3"; "logic"];
  so note("L",{%fol||--(imp(Pr(G),F))|}) by ["consistency"; "logic"];
  so have {%fol||--(G)|} by ["fix2"; "logic"];
  so have {%fol||--(Pr(G))|} by ["lob1"; "logic"];
  so conclude {%fol||--(F)|} by ["L"; "logic"];
  qed];;
