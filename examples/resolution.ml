(* Interactive examples from resolution.ml, lifted out of the source by
   tools/migrate_to_modules.py.  Not compiled: these are meant to be
   pasted into a toplevel that has opened Atp.All. *)

simpcnf(skolemize(Not barb));;

(* ---- *)

let davis_putnam_example = resolution
 {%fol|exists x. exists y. forall z.
        (F(x,y) ==> (F(y,z) /\ F(z,z))) /\
        ((F(x,y) /\ G(x,y)) ==> (G(x,z) /\ G(z,z)))|};;

(* ---- *)

let davis_putnam_example = resolution
 {%fol|exists x. exists y. forall z.
        (F(x,y) ==> (F(y,z) /\ F(z,z))) /\
        ((F(x,y) /\ G(x,y)) ==> (G(x,z) /\ G(z,z)))|};;

(* ---- *)

let los = time presolution
 {%fol|(forall x y z. P(x,y) ==> P(y,z) ==> P(x,z)) /\
   (forall x y z. Q(x,y) ==> Q(y,z) ==> Q(x,z)) /\
   (forall x y. Q(x,y) ==> Q(y,x)) /\
   (forall x y. P(x,y) \/ Q(x,y))
   ==> (forall x y. P(x,y)) \/ (forall x y. Q(x,y))|};;

(* ------------------------------------------------------------------------- *)
(* Introduce a set-of-support restriction.                                   *)
(* ------------------------------------------------------------------------- *)

let pure_resolution fm =
  resloop(partition (exists positive) (simpcnf(specialize(pnf fm))));;

let resolution fm =
  let fm1 = askolemize(Not(generalize fm)) in
  map (pure_resolution ** list_conj) (simpdnf fm1);;

(* ------------------------------------------------------------------------- *)
(* The Pelletier examples again.                                             *)
(* ------------------------------------------------------------------------- *)

(***********

let p1 = time presolution
 {%fol|p ==> q <=> ~q ==> ~p|};;

let p2 = time presolution
 {%fol|~ ~p <=> p|};;

let p3 = time presolution
 {%fol|~(p ==> q) ==> q ==> p|};;

let p4 = time presolution
 {%fol|~p ==> q <=> ~q ==> p|};;

let p5 = time presolution
 {%fol|(p \/ q ==> p \/ r) ==> p \/ (q ==> r)|};;

let p6 = time presolution
 {%fol|p \/ ~p|};;

let p7 = time presolution
 {%fol|p \/ ~ ~ ~p|};;

let p8 = time presolution
 {%fol|((p ==> q) ==> p) ==> p|};;

let p9 = time presolution
 {%fol|(p \/ q) /\ (~p \/ q) /\ (p \/ ~q) ==> ~(~q \/ ~q)|};;

let p10 = time presolution
 {%fol|(q ==> r) /\ (r ==> p /\ q) /\ (p ==> q /\ r) ==> (p <=> q)|};;

let p11 = time presolution
 {%fol|p <=> p|};;

let p12 = time presolution
 {%fol|((p <=> q) <=> r) <=> (p <=> (q <=> r))|};;

let p13 = time presolution
 {%fol|p \/ q /\ r <=> (p \/ q) /\ (p \/ r)|};;

let p14 = time presolution
 {%fol|(p <=> q) <=> (q \/ ~p) /\ (~q \/ p)|};;

let p15 = time presolution
 {%fol|p ==> q <=> ~p \/ q|};;

let p16 = time presolution
 {%fol|(p ==> q) \/ (q ==> p)|};;

let p17 = time presolution
 {%fol|p /\ (q ==> r) ==> s <=> (~p \/ q \/ s) /\ (~p \/ ~r \/ s)|};;

(* ------------------------------------------------------------------------- *)
(* Monadic Predicate Logic.                                                  *)
(* ------------------------------------------------------------------------- *)

let p18 = time presolution
 {%fol|exists y. forall x. P(y) ==> P(x)|};;

let p19 = time presolution
 {%fol|exists x. forall y z. (P(y) ==> Q(z)) ==> P(x) ==> Q(x)|};;

let p20 = time presolution
 {%fol|(forall x y. exists z. forall w. P(x) /\ Q(y) ==> R(z) /\ U(w))
   ==> (exists x y. P(x) /\ Q(y)) ==> (exists z. R(z))|};;

let p21 = time presolution
 {%fol|(exists x. P ==> Q(x)) /\ (exists x. Q(x) ==> P)
   ==> (exists x. P <=> Q(x))|};;

let p22 = time presolution
 {%fol|(forall x. P <=> Q(x)) ==> (P <=> (forall x. Q(x)))|};;

let p23 = time presolution
 {%fol|(forall x. P \/ Q(x)) <=> P \/ (forall x. Q(x))|};;

let p24 = time presolution
 {%fol|~(exists x. U(x) /\ Q(x)) /\
   (forall x. P(x) ==> Q(x) \/ R(x)) /\
   ~(exists x. P(x) ==> (exists x. Q(x))) /\
   (forall x. Q(x) /\ R(x) ==> U(x)) ==>
   (exists x. P(x) /\ R(x))|};;

let p25 = time presolution
 {%fol|(exists x. P(x)) /\
   (forall x. U(x) ==> ~G(x) /\ R(x)) /\
   (forall x. P(x) ==> G(x) /\ U(x)) /\
   ((forall x. P(x) ==> Q(x)) \/ (exists x. Q(x) /\ P(x))) ==>
   (exists x. Q(x) /\ P(x))|};;

let p26 = time presolution
 {%fol|((exists x. P(x)) <=> (exists x. Q(x))) /\
   (forall x y. P(x) /\ Q(y) ==> (R(x) <=> U(y))) ==>
   ((forall x. P(x) ==> R(x)) <=> (forall x. Q(x) ==> U(x)))|};;

let p27 = time presolution
 {%fol|(exists x. P(x) /\ ~Q(x)) /\
   (forall x. P(x) ==> R(x)) /\
   (forall x. U(x) /\ V(x) ==> P(x)) /\
   (exists x. R(x) /\ ~Q(x)) ==>
   (forall x. U(x) ==> ~R(x)) ==>
   (forall x. U(x) ==> ~V(x))|};;

let p28 = time presolution
 {%fol|(forall x. P(x) ==> (forall x. Q(x))) /\
   ((forall x. Q(x) \/ R(x)) ==> (exists x. Q(x) /\ R(x))) /\
   ((exists x. R(x)) ==> (forall x. L(x) ==> M(x))) ==>
   (forall x. P(x) /\ L(x) ==> M(x))|};;

let p29 = time presolution
 {%fol|(exists x. P(x)) /\ (exists x. G(x)) ==>
   ((forall x. P(x) ==> H(x)) /\ (forall x. G(x) ==> J(x)) <=>
    (forall x y. P(x) /\ G(y) ==> H(x) /\ J(y)))|};;

let p30 = time presolution
 {%fol|(forall x. P(x) \/ G(x) ==> ~H(x)) /\
   (forall x. (G(x) ==> ~U(x)) ==> P(x) /\ H(x)) ==>
   (forall x. U(x))|};;

let p31 = time presolution
 {%fol|~(exists x. P(x) /\ (G(x) \/ H(x))) /\ (exists x. Q(x) /\ P(x)) /\
   (forall x. ~H(x) ==> J(x)) ==>
   (exists x. Q(x) /\ J(x))|};;

let p32 = time presolution
 {%fol|(forall x. P(x) /\ (G(x) \/ H(x)) ==> Q(x)) /\
   (forall x. Q(x) /\ H(x) ==> J(x)) /\
   (forall x. R(x) ==> H(x)) ==>
   (forall x. P(x) /\ R(x) ==> J(x))|};;

let p33 = time presolution
 {%fol|(forall x. P(a) /\ (P(x) ==> P(b)) ==> P(c)) <=>
   (forall x. P(a) ==> P(x) \/ P(c)) /\ (P(a) ==> P(b) ==> P(c))|};;

let p34 = time presolution
 {%fol|((exists x. forall y. P(x) <=> P(y)) <=>
    ((exists x. Q(x)) <=> (forall y. Q(y)))) <=>
   ((exists x. forall y. Q(x) <=> Q(y)) <=>
    ((exists x. P(x)) <=> (forall y. P(y))))|};;

let p35 = time presolution
 {%fol|exists x y. P(x,y) ==> (forall x y. P(x,y))|};;

(* ------------------------------------------------------------------------- *)
(*  Full predicate logic (without Identity and Functions)                    *)
(* ------------------------------------------------------------------------- *)

let p36 = time presolution
 {%fol|(forall x. exists y. P(x,y)) /\
   (forall x. exists y. G(x,y)) /\
   (forall x y. P(x,y) \/ G(x,y)
   ==> (forall z. P(y,z) \/ G(y,z) ==> H(x,z)))
       ==> (forall x. exists y. H(x,y))|};;

let p37 = time presolution
 {%fol|(forall z.
     exists w. forall x. exists y. (P(x,z) ==> P(y,w)) /\ P(y,z) /\
     (P(y,w) ==> (exists u. Q(u,w)))) /\
   (forall x z. ~P(x,z) ==> (exists y. Q(y,z))) /\
   ((exists x y. Q(x,y)) ==> (forall x. R(x,x))) ==>
   (forall x. exists y. R(x,y))|};;

(*** This one seems too slow

let p38 = time presolution
 {%fol|(forall x.
     P(a) /\ (P(x) ==> (exists y. P(y) /\ R(x,y))) ==>
     (exists z w. P(z) /\ R(x,w) /\ R(w,z))) <=>
   (forall x.
     (~P(a) \/ P(x) \/ (exists z w. P(z) /\ R(x,w) /\ R(w,z))) /\
     (~P(a) \/ ~(exists y. P(y) /\ R(x,y)) \/
     (exists z w. P(z) /\ R(x,w) /\ R(w,z))))|};;

 ***)

let p39 = time presolution
 {%fol|~(exists x. forall y. P(y,x) <=> ~P(y,y))|};;

let p40 = time presolution
 {%fol|(exists y. forall x. P(x,y) <=> P(x,x))
  ==> ~(forall x. exists y. forall z. P(z,y) <=> ~P(z,x))|};;

let p41 = time presolution
 {%fol|(forall z. exists y. forall x. P(x,y) <=> P(x,z) /\ ~P(x,x))
  ==> ~(exists z. forall x. P(x,z))|};;

(*** Also very slow

let p42 = time presolution
 {%fol|~(exists y. forall x. P(x,y) <=> ~(exists z. P(x,z) /\ P(z,x)))|};;

 ***)

(*** and this one too..

let p43 = time presolution
 {%fol|(forall x y. Q(x,y) <=> forall z. P(z,x) <=> P(z,y))
   ==> forall x y. Q(x,y) <=> Q(y,x)|};;

 ***)

let p44 = time presolution
 {%fol|(forall x. P(x) ==> (exists y. G(y) /\ H(x,y)) /\
   (exists y. G(y) /\ ~H(x,y))) /\
   (exists x. J(x) /\ (forall y. G(y) ==> H(x,y))) ==>
   (exists x. J(x) /\ ~P(x))|};;

(*** and this...

let p45 = time presolution
 {%fol|(forall x.
     P(x) /\ (forall y. G(y) /\ H(x,y) ==> J(x,y)) ==>
       (forall y. G(y) /\ H(x,y) ==> R(y))) /\
   ~(exists y. L(y) /\ R(y)) /\
   (exists x. P(x) /\ (forall y. H(x,y) ==>
     L(y)) /\ (forall y. G(y) /\ H(x,y) ==> J(x,y))) ==>
   (exists x. P(x) /\ ~(exists y. G(y) /\ H(x,y)))|};;

 ***)

(*** and this

let p46 = time presolution
 {%fol|(forall x. P(x) /\ (forall y. P(y) /\ H(y,x) ==> G(y)) ==> G(x)) /\
   ((exists x. P(x) /\ ~G(x)) ==>
    (exists x. P(x) /\ ~G(x) /\
               (forall y. P(y) /\ ~G(y) ==> J(x,y)))) /\
   (forall x y. P(x) /\ P(y) /\ H(x,y) ==> ~J(y,x)) ==>
   (forall x. P(x) ==> G(x))|};;

 ***)

(* ------------------------------------------------------------------------- *)
(* Example from Manthey and Bry, CADE-9.                                     *)
(* ------------------------------------------------------------------------- *)

let p55 = time presolution
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
       ~killed(charles,agatha)|};;

let p57 = time presolution
 {%fol|P(f((a),b),f(b,c)) /\
   P(f(b,c),f(a,c)) /\
   (forall (x) y z. P(x,y) /\ P(y,z) ==> P(x,z))
   ==> P(f(a,b),f(a,c))|};;

(* ------------------------------------------------------------------------- *)
(* See info-hol, circa 1500.                                                 *)
(* ------------------------------------------------------------------------- *)

let p58 = time presolution
 {%fol|forall P Q R. forall x. exists v. exists w. forall y. forall z.
    ((P(x) /\ Q(y)) ==> ((P(v) \/ R(w))  /\ (R(z) ==> Q(v))))|};;

let p59 = time presolution
 {%fol|(forall x. P(x) <=> ~P(f(x))) ==> (exists x. P(x) /\ ~P(f(x)))|};;

let p60 = time presolution
 {%fol|forall x. P(x,f(x)) <=>
            exists y. (forall z. P(z,y) ==> P(z,f(x))) /\ P(x,y)|};;

(* ------------------------------------------------------------------------- *)
(* From Gilmore's classic paper.                                             *)
(* ------------------------------------------------------------------------- *)

let gilmore_1 = time presolution
 {%fol|exists x. forall y z.
      ((F(y) ==> G(y)) <=> F(x)) /\
      ((F(y) ==> H(y)) <=> G(x)) /\
      (((F(y) ==> G(y)) ==> H(y)) <=> H(x))
      ==> F(z) /\ G(z) /\ H(z)|};;

(*** This is not valid, according to Gilmore

let gilmore_2 = time presolution
 {%fol|exists x y. forall z.
        (F(x,z) <=> F(z,y)) /\ (F(z,y) <=> F(z,z)) /\ (F(x,y) <=> F(y,x))
        ==> (F(x,y) <=> F(x,z))|};;

 ***)

let gilmore_3 = time presolution
 {%fol|exists x. forall y z.
        ((F(y,z) ==> (G(y) ==> H(x))) ==> F(x,x)) /\
        ((F(z,x) ==> G(x)) ==> H(z)) /\
        F(x,y)
        ==> F(z,z)|};;

let gilmore_4 = time presolution
 {%fol|exists x y. forall z.
        (F(x,y) ==> F(y,z) /\ F(z,z)) /\
        (F(x,y) /\ G(x,y) ==> G(x,z) /\ G(z,z))|};;

let gilmore_5 = time presolution
 {%fol|(forall x. exists y. F(x,y) \/ F(y,x)) /\
   (forall x y. F(y,x) ==> F(y,y))
   ==> exists z. F(z,z)|};;

let gilmore_6 = time presolution
 {%fol|forall x. exists y.
        (exists u. forall v. F(u,x) ==> G(v,u) /\ G(u,x))
        ==> (exists u. forall v. F(u,y) ==> G(v,u) /\ G(u,y)) \/
            (forall u v. exists w. G(v,u) \/ H(w,y,u) ==> G(u,w))|};;

let gilmore_7 = time presolution
 {%fol|(forall x. K(x) ==> exists y. L(y) /\ (F(x,y) ==> G(x,y))) /\
   (exists z. K(z) /\ forall u. L(u) ==> F(z,u))
   ==> exists v w. K(v) /\ L(w) /\ G(v,w)|};;

let gilmore_8 = time presolution
 {%fol|exists x. forall y z.
        ((F(y,z) ==> (G(y) ==> (forall u. exists v. H(u,v,x)))) ==> F(x,x)) /\
        ((F(z,x) ==> G(x)) ==> (forall u. exists v. H(u,v,z))) /\
        F(x,y)
        ==> F(z,z)|};;

(*** This one still isn't easy!

let gilmore_9 = time presolution
 {%fol|forall x. exists y. forall z.
        ((forall u. exists v. F(y,u,v) /\ G(y,u) /\ ~H(y,x))
          ==> (forall u. exists v. F(x,u,v) /\ G(z,u) /\ ~H(x,z))
             ==> (forall u. exists v. F(x,u,v) /\ G(y,u) /\ ~H(x,y))) /\
        ((forall u. exists v. F(x,u,v) /\ G(y,u) /\ ~H(x,y))
         ==> ~(forall u. exists v. F(x,u,v) /\ G(z,u) /\ ~H(x,z))
             ==> (forall u. exists v. F(y,u,v) /\ G(y,u) /\ ~H(y,x)) /\
                 (forall u. exists v. F(z,u,v) /\ G(y,u) /\ ~H(z,y)))|};;

 ***)

(* ------------------------------------------------------------------------- *)
(* Example from Davis-Putnam papers where Gilmore procedure is poor.         *)
(* ------------------------------------------------------------------------- *)

let davis_putnam_example = time presolution
 {%fol|exists x. exists y. forall z.
        (F(x,y) ==> (F(y,z) /\ F(z,z))) /\
        ((F(x,y) /\ G(x,y)) ==> (G(x,z) /\ G(z,z)))|};;

************)

(* ---- *)

let gilmore_1 = resolution
 {%fol|exists x. forall y z.
      ((F(y) ==> G(y)) <=> F(x)) /\
      ((F(y) ==> H(y)) <=> G(x)) /\
      (((F(y) ==> G(y)) ==> H(y)) <=> H(x))
      ==> F(z) /\ G(z) /\ H(z)|};;

(* ------------------------------------------------------------------------- *)
(* Pelletiers yet again.                                                     *)
(* ------------------------------------------------------------------------- *)

(************

let p1 = time resolution
 {%fol|p ==> q <=> ~q ==> ~p|};;

let p2 = time resolution
 {%fol|~ ~p <=> p|};;

let p3 = time resolution
 {%fol|~(p ==> q) ==> q ==> p|};;

let p4 = time resolution
 {%fol|~p ==> q <=> ~q ==> p|};;

let p5 = time resolution
 {%fol|(p \/ q ==> p \/ r) ==> p \/ (q ==> r)|};;

let p6 = time resolution
 {%fol|p \/ ~p|};;

let p7 = time resolution
 {%fol|p \/ ~ ~ ~p|};;

let p8 = time resolution
 {%fol|((p ==> q) ==> p) ==> p|};;

let p9 = time resolution
 {%fol|(p \/ q) /\ (~p \/ q) /\ (p \/ ~q) ==> ~(~q \/ ~q)|};;

let p10 = time resolution
 {%fol|(q ==> r) /\ (r ==> p /\ q) /\ (p ==> q /\ r) ==> (p <=> q)|};;

let p11 = time resolution
 {%fol|p <=> p|};;

let p12 = time resolution
 {%fol|((p <=> q) <=> r) <=> (p <=> (q <=> r))|};;

let p13 = time resolution
 {%fol|p \/ q /\ r <=> (p \/ q) /\ (p \/ r)|};;

let p14 = time resolution
 {%fol|(p <=> q) <=> (q \/ ~p) /\ (~q \/ p)|};;

let p15 = time resolution
 {%fol|p ==> q <=> ~p \/ q|};;

let p16 = time resolution
 {%fol|(p ==> q) \/ (q ==> p)|};;

let p17 = time resolution
 {%fol|p /\ (q ==> r) ==> s <=> (~p \/ q \/ s) /\ (~p \/ ~r \/ s)|};;

(* ------------------------------------------------------------------------- *)
(* Monadic Predicate Logic.                                                  *)
(* ------------------------------------------------------------------------- *)

let p18 = time resolution
 {%fol|exists y. forall x. P(y) ==> P(x)|};;

let p19 = time resolution
 {%fol|exists x. forall y z. (P(y) ==> Q(z)) ==> P(x) ==> Q(x)|};;

let p20 = time resolution
 {%fol|(forall x y. exists z. forall w. P(x) /\ Q(y) ==> R(z) /\ U(w)) ==>
   (exists x y. P(x) /\ Q(y)) ==>
   (exists z. R(z))|};;

let p21 = time resolution
 {%fol|(exists x. P ==> Q(x)) /\ (exists x. Q(x) ==> P) ==> (exists x. P <=> Q(x))|};;

let p22 = time resolution
 {%fol|(forall x. P <=> Q(x)) ==> (P <=> (forall x. Q(x)))|};;

let p23 = time resolution
 {%fol|(forall x. P \/ Q(x)) <=> P \/ (forall x. Q(x))|};;

let p24 = time resolution
 {%fol|~(exists x. U(x) /\ Q(x)) /\
   (forall x. P(x) ==> Q(x) \/ R(x)) /\
   ~(exists x. P(x) ==> (exists x. Q(x))) /\
   (forall x. Q(x) /\ R(x) ==> U(x)) ==>
   (exists x. P(x) /\ R(x))|};;

let p25 = time resolution
 {%fol|(exists x. P(x)) /\
   (forall x. U(x) ==> ~G(x) /\ R(x)) /\
   (forall x. P(x) ==> G(x) /\ U(x)) /\
   ((forall x. P(x) ==> Q(x)) \/ (exists x. Q(x) /\ P(x))) ==>
   (exists x. Q(x) /\ P(x))|};;

let p26 = time resolution
 {%fol|((exists x. P(x)) <=> (exists x. Q(x))) /\
   (forall x y. P(x) /\ Q(y) ==> (R(x) <=> U(y))) ==>
   ((forall x. P(x) ==> R(x)) <=> (forall x. Q(x) ==> U(x)))|};;

let p27 = time resolution
 {%fol|(exists x. P(x) /\ ~Q(x)) /\
   (forall x. P(x) ==> R(x)) /\
   (forall x. U(x) /\ V(x) ==> P(x)) /\
   (exists x. R(x) /\ ~Q(x)) ==>
   (forall x. U(x) ==> ~R(x)) ==>
   (forall x. U(x) ==> ~V(x))|};;

let p28 = time resolution
 {%fol|(forall x. P(x) ==> (forall x. Q(x))) /\
   ((forall x. Q(x) \/ R(x)) ==> (exists x. Q(x) /\ R(x))) /\
   ((exists x. R(x)) ==> (forall x. L(x) ==> M(x))) ==>
   (forall x. P(x) /\ L(x) ==> M(x))|};;

let p29 = time resolution
 {%fol|(exists x. P(x)) /\ (exists x. G(x)) ==>
   ((forall x. P(x) ==> H(x)) /\ (forall x. G(x) ==> J(x)) <=>
    (forall x y. P(x) /\ G(y) ==> H(x) /\ J(y)))|};;

let p30 = time resolution
 {%fol|(forall x. P(x) \/ G(x) ==> ~H(x)) /\ (forall x. (G(x) ==> ~U(x)) ==>
     P(x) /\ H(x)) ==>
   (forall x. U(x))|};;

let p31 = time resolution
 {%fol|~(exists x. P(x) /\ (G(x) \/ H(x))) /\ (exists x. Q(x) /\ P(x)) /\
   (forall x. ~H(x) ==> J(x)) ==>
   (exists x. Q(x) /\ J(x))|};;

let p32 = time resolution
 {%fol|(forall x. P(x) /\ (G(x) \/ H(x)) ==> Q(x)) /\
   (forall x. Q(x) /\ H(x) ==> J(x)) /\
   (forall x. R(x) ==> H(x)) ==>
   (forall x. P(x) /\ R(x) ==> J(x))|};;

let p33 = time resolution
 {%fol|(forall x. P(a) /\ (P(x) ==> P(b)) ==> P(c)) <=>
   (forall x. P(a) ==> P(x) \/ P(c)) /\ (P(a) ==> P(b) ==> P(c))|};;

let p34 = time resolution
 {%fol|((exists x. forall y. P(x) <=> P(y)) <=>
   ((exists x. Q(x)) <=> (forall y. Q(y)))) <=>
   ((exists x. forall y. Q(x) <=> Q(y)) <=>
  ((exists x. P(x)) <=> (forall y. P(y))))|};;

let p35 = time resolution
 {%fol|exists x y. P(x,y) ==> (forall x y. P(x,y))|};;

(* ------------------------------------------------------------------------- *)
(*  Full predicate logic (without Identity and Functions)                    *)
(* ------------------------------------------------------------------------- *)

let p36 = time resolution
 {%fol|(forall x. exists y. P(x,y)) /\
   (forall x. exists y. G(x,y)) /\
   (forall x y. P(x,y) \/ G(x,y)
   ==> (forall z. P(y,z) \/ G(y,z) ==> H(x,z)))
       ==> (forall x. exists y. H(x,y))|};;

let p37 = time resolution
 {%fol|(forall z.
     exists w. forall x. exists y. (P(x,z) ==> P(y,w)) /\ P(y,z) /\
     (P(y,w) ==> (exists u. Q(u,w)))) /\
   (forall x z. ~P(x,z) ==> (exists y. Q(y,z))) /\
   ((exists x y. Q(x,y)) ==> (forall x. R(x,x))) ==>
   (forall x. exists y. R(x,y))|};;

(*** This one seems too slow

let p38 = time resolution
 {%fol|(forall x.
     P(a) /\ (P(x) ==> (exists y. P(y) /\ R(x,y))) ==>
     (exists z w. P(z) /\ R(x,w) /\ R(w,z))) <=>
   (forall x.
     (~P(a) \/ P(x) \/ (exists z w. P(z) /\ R(x,w) /\ R(w,z))) /\
     (~P(a) \/ ~(exists y. P(y) /\ R(x,y)) \/
     (exists z w. P(z) /\ R(x,w) /\ R(w,z))))|};;

 ***)

let p39 = time resolution
 {%fol|~(exists x. forall y. P(y,x) <=> ~P(y,y))|};;

let p40 = time resolution
 {%fol|(exists y. forall x. P(x,y) <=> P(x,x))
  ==> ~(forall x. exists y. forall z. P(z,y) <=> ~P(z,x))|};;

let p41 = time resolution
 {%fol|(forall z. exists y. forall x. P(x,y) <=> P(x,z) /\ ~P(x,x))
  ==> ~(exists z. forall x. P(x,z))|};;

(*** Also very slow

let p42 = time resolution
 {%fol|~(exists y. forall x. P(x,y) <=> ~(exists z. P(x,z) /\ P(z,x)))|};;

 ***)

(*** and this one too..

let p43 = time resolution
 {%fol|(forall x y. Q(x,y) <=> forall z. P(z,x) <=> P(z,y))
   ==> forall x y. Q(x,y) <=> Q(y,x)|};;

 ***)

let p44 = time resolution
 {%fol|(forall x. P(x) ==> (exists y. G(y) /\ H(x,y)) /\
   (exists y. G(y) /\ ~H(x,y))) /\
   (exists x. J(x) /\ (forall y. G(y) ==> H(x,y))) ==>
   (exists x. J(x) /\ ~P(x))|};;

(*** and this...

let p45 = time resolution
 {%fol|(forall x.
     P(x) /\ (forall y. G(y) /\ H(x,y) ==> J(x,y)) ==>
       (forall y. G(y) /\ H(x,y) ==> R(y))) /\
   ~(exists y. L(y) /\ R(y)) /\
   (exists x. P(x) /\ (forall y. H(x,y) ==>
     L(y)) /\ (forall y. G(y) /\ H(x,y) ==> J(x,y))) ==>
   (exists x. P(x) /\ ~(exists y. G(y) /\ H(x,y)))|};;

 ***)

(*** and this

let p46 = time resolution
 {%fol|(forall x. P(x) /\ (forall y. P(y) /\ H(y,x) ==> G(y)) ==> G(x)) /\
   ((exists x. P(x) /\ ~G(x)) ==>
    (exists x. P(x) /\ ~G(x) /\
               (forall y. P(y) /\ ~G(y) ==> J(x,y)))) /\
   (forall x y. P(x) /\ P(y) /\ H(x,y) ==> ~J(y,x)) ==>
   (forall x. P(x) ==> G(x))|};;

 ***)

(* ------------------------------------------------------------------------- *)
(* Example from Manthey and Bry, CADE-9.                                     *)
(* ------------------------------------------------------------------------- *)

let p55 = time resolution
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
       ~killed(charles,agatha)|};;

let p57 = time resolution
 {%fol|P(f((a),b),f(b,c)) /\
   P(f(b,c),f(a,c)) /\
   (forall (x) y z. P(x,y) /\ P(y,z) ==> P(x,z))
   ==> P(f(a,b),f(a,c))|};;

(* ------------------------------------------------------------------------- *)
(* See info-hol, circa 1500.                                                 *)
(* ------------------------------------------------------------------------- *)

let p58 = time resolution
 {%fol|forall P Q R. forall x. exists v. exists w. forall y. forall z.
    ((P(x) /\ Q(y)) ==> ((P(v) \/ R(w))  /\ (R(z) ==> Q(v))))|};;

let p59 = time resolution
 {%fol|(forall x. P(x) <=> ~P(f(x))) ==> (exists x. P(x) /\ ~P(f(x)))|};;

let p60 = time resolution
 {%fol|forall x. P(x,f(x)) <=>
            exists y. (forall z. P(z,y) ==> P(z,f(x))) /\ P(x,y)|};;

(* ------------------------------------------------------------------------- *)
(* From Gilmore's classic paper.                                             *)
(* ------------------------------------------------------------------------- *)

let gilmore_1 = time resolution
 {%fol|exists x. forall y z.
      ((F(y) ==> G(y)) <=> F(x)) /\
      ((F(y) ==> H(y)) <=> G(x)) /\
      (((F(y) ==> G(y)) ==> H(y)) <=> H(x))
      ==> F(z) /\ G(z) /\ H(z)|};;

(*** This is not valid, according to Gilmore

let gilmore_2 = time resolution
 {%fol|exists x y. forall z.
        (F(x,z) <=> F(z,y)) /\ (F(z,y) <=> F(z,z)) /\ (F(x,y) <=> F(y,x))
        ==> (F(x,y) <=> F(x,z))|};;

 ***)

let gilmore_3 = time resolution
 {%fol|exists x. forall y z.
        ((F(y,z) ==> (G(y) ==> H(x))) ==> F(x,x)) /\
        ((F(z,x) ==> G(x)) ==> H(z)) /\
        F(x,y)
        ==> F(z,z)|};;

let gilmore_4 = time resolution
 {%fol|exists x y. forall z.
        (F(x,y) ==> F(y,z) /\ F(z,z)) /\
        (F(x,y) /\ G(x,y) ==> G(x,z) /\ G(z,z))|};;

let gilmore_5 = time resolution
 {%fol|(forall x. exists y. F(x,y) \/ F(y,x)) /\
   (forall x y. F(y,x) ==> F(y,y))
   ==> exists z. F(z,z)|};;

let gilmore_6 = time resolution
 {%fol|forall x. exists y.
        (exists u. forall v. F(u,x) ==> G(v,u) /\ G(u,x))
        ==> (exists u. forall v. F(u,y) ==> G(v,u) /\ G(u,y)) \/
            (forall u v. exists w. G(v,u) \/ H(w,y,u) ==> G(u,w))|};;

let gilmore_7 = time resolution
 {%fol|(forall x. K(x) ==> exists y. L(y) /\ (F(x,y) ==> G(x,y))) /\
   (exists z. K(z) /\ forall u. L(u) ==> F(z,u))
   ==> exists v w. K(v) /\ L(w) /\ G(v,w)|};;

let gilmore_8 = time resolution
 {%fol|exists x. forall y z.
        ((F(y,z) ==> (G(y) ==> (forall u. exists v. H(u,v,x)))) ==> F(x,x)) /\
        ((F(z,x) ==> G(x)) ==> (forall u. exists v. H(u,v,z))) /\
        F(x,y)
        ==> F(z,z)|};;

(*** This one still isn't easy!

let gilmore_9 = time resolution
 {%fol|forall x. exists y. forall z.
        ((forall u. exists v. F(y,u,v) /\ G(y,u) /\ ~H(y,x))
          ==> (forall u. exists v. F(x,u,v) /\ G(z,u) /\ ~H(x,z))
             ==> (forall u. exists v. F(x,u,v) /\ G(y,u) /\ ~H(x,y))) /\
        ((forall u. exists v. F(x,u,v) /\ G(y,u) /\ ~H(x,y))
         ==> ~(forall u. exists v. F(x,u,v) /\ G(z,u) /\ ~H(x,z))
             ==> (forall u. exists v. F(y,u,v) /\ G(y,u) /\ ~H(y,x)) /\
                 (forall u. exists v. F(z,u,v) /\ G(y,u) /\ ~H(z,y)))|};;

 ***)

(* ------------------------------------------------------------------------- *)
(* Example from Davis-Putnam papers where Gilmore procedure is poor.         *)
(* ------------------------------------------------------------------------- *)

let davis_putnam_example = time resolution
 {%fol|exists x. exists y. forall z.
        (F(x,y) ==> (F(y,z) /\ F(z,z))) /\
        ((F(x,y) /\ G(x,y)) ==> (G(x,z) /\ G(z,z)))|};;

(* ------------------------------------------------------------------------- *)
(* The (in)famous Los problem.                                               *)
(* ------------------------------------------------------------------------- *)

let los = time resolution
 {%fol|(forall x y z. P(x,y) ==> P(y,z) ==> P(x,z)) /\
   (forall x y z. Q(x,y) ==> Q(y,z) ==> Q(x,z)) /\
   (forall x y. Q(x,y) ==> Q(y,x)) /\
   (forall x y. P(x,y) \/ Q(x,y))
   ==> (forall x y. P(x,y)) \/ (forall x y. Q(x,y))|};;

**************)
