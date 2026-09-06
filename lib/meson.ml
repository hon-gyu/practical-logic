open Lib
open Formulas
open Prop
open Fol
open Skolem
open Tableaux
open Prolog

(* Warnings the book's style trips in this file; the rest of the
   library compiles with them on.  See lib/dune. *)
[@@@warning "-10-32-39"]

(* ========================================================================= *)
(* Model elimination procedure (MESON version, based on Stickel's PTTP).     *)
(*                                                                           *)
(* Copyright (c) 2003-2007, John Harrison. (See "LICENSE.txt" for details.)  *)
(* ========================================================================= *)

let%expect_test "eg: naivety of tableau prover" =
  print_fol_formula
    (tab {%fol|forall a. ~(P(a) /\ (forall y z. Q(y) \/ R(z)) /\ ~P(a))|});
  print_fol_formula
    (tab {%fol|forall a. ~(P(a) /\ ~P(a) /\ (forall y z. Q(y) \/ R(z)))|});
  (* ------------------------------------------------------------------------- *)
  (* The interesting example where tableaux connections make the proof longer. *)
  (* Unfortuntely this gets hammered by normalization first...                 *)
  (* ------------------------------------------------------------------------- *)
  print_fol_formula
    (tab {%fol|~p /\ (p \/ q) /\ (r \/ s) /\ (~q \/ t \/ u) /\
          (~r \/ ~t) /\ (~r \/ ~u) /\ (~q \/ v \/ w) /\
          (~s \/ ~v) /\ (~s \/ ~w) ==> false|});
  [%expect {| |}]
;;

(* ------------------------------------------------------------------------- *)
(* Generation of contrapositives.                                            *)
(* ------------------------------------------------------------------------- *)

let contrapositives cls =
  let base = map (fun c -> map negate (subtract cls [c]),c) cls in
  if forall negative cls then (map negate cls,False)::base else base;;

(* ------------------------------------------------------------------------- *)
(* The core of MESON: ancestor unification or Prolog-style extension.        *)
(* ------------------------------------------------------------------------- *)

let rec mexpand rules ancestors g cont (env,n,k) =
  if n < 0 then failwith "Too deep" else
  try tryfind (fun a -> cont (unify_literals env (g,negate a),n,k))
              ancestors
  with Failure _ -> tryfind
    (fun rule -> let (asm,c),k' = renamerule k rule in
                 itlist (mexpand rules (g::ancestors)) asm cont
                        (unify_literals env (g,c),n-length asm,k'))
    rules;;

(* ------------------------------------------------------------------------- *)
(* Full MESON procedure.                                                     *)
(* ------------------------------------------------------------------------- *)

let puremeson fm =
  let cls = simpcnf(specialize(pnf fm)) in
  let rules = itlist ((@) ** contrapositives) cls [] in
  deepen (fun n ->
     mexpand rules [] False (fun x -> x) (undefined,n,0); n) 0;;

let meson fm =
  let fm1 = askolemize(Not(generalize fm)) in
  map (puremeson ** list_conj) (simpdnf fm1);;

let%expect_test "eg" =
  let davis_putnam_example = meson
   {%fol|exists x. exists y. forall z.
          (F(x,y) ==> (F(y,z) /\ F(z,z))) /\
          ((F(x,y) /\ G(x,y)) ==> (G(x,z) /\ G(z,z)))|} in
  print_fol_formula
    (davis_putnam_example);
  [%expect {| |}]
;;


(* ------------------------------------------------------------------------- *)
(* With repetition checking and divide-and-conquer search.                   *)
(* ------------------------------------------------------------------------- *)

let rec equal env fm1 fm2 =
  try unify_literals env (fm1,fm2) == env with Failure _ -> false;;

let expand2 expfn goals1 n1 goals2 n2 n3 cont env k =
   expfn goals1 (fun (e1,r1,k1) ->
        expfn goals2 (fun (e2,r2,k2) ->
                        if n2 + r1 <= n3 + r2 then failwith "pair"
                        else cont(e2,r2,k2))
              (e1,n2+r1,k1))
        (env,n1,k);;

let rec mexpand rules ancestors g cont (env,n,k) =
  if n < 0 then failwith "Too deep"
  else if exists (equal env g) ancestors then failwith "repetition" else
  try tryfind (fun a -> cont (unify_literals env (g,negate a),n,k))
              ancestors
  with Failure _ -> tryfind
    (fun r -> let (asm,c),k' = renamerule k r in
              mexpands rules (g::ancestors) asm cont
                       (unify_literals env (g,c),n-length asm,k'))
    rules

and mexpands rules ancestors gs cont (env,n,k) =
  if n < 0 then failwith "Too deep" else
  let m = length gs in
  if m <= 1 then itlist (mexpand rules ancestors) gs cont (env,n,k) else
  let n1 = n / 2 in
  let n2 = n - n1 in
  let goals1,goals2 = chop_list (m / 2) gs in
  let expfn = expand2 (mexpands rules ancestors) in
  try expfn goals1 n1 goals2 n2 (-1) cont env k
  with Failure _ -> expfn goals2 n1 goals1 n2 n1 cont env k;;

let puremeson fm =
  let cls = simpcnf(specialize(pnf fm)) in
  let rules = itlist ((@) ** contrapositives) cls [] in
  deepen (fun n ->
     mexpand rules [] False (fun x -> x) (undefined,n,0); n) 0;;

let meson fm =
  let fm1 = askolemize(Not(generalize fm)) in
  map (puremeson ** list_conj) (simpdnf fm1);;

(* ------------------------------------------------------------------------- *)
(* The Los problem (depth 20) and the Steamroller (depth 53) --- lengthier.  *)
(* ------------------------------------------------------------------------- *)

let%expect_test "eg: The Los problem (depth 20) and the Steamroller (depth 53) --- lengthier" =
  (***********

  let los = meson
   {%fol|(forall x y z. P(x,y) ==> P(y,z) ==> P(x,z)) /\
     (forall x y z. Q(x,y) ==> Q(y,z) ==> Q(x,z)) /\
     (forall x y. Q(x,y) ==> Q(y,x)) /\
     (forall x y. P(x,y) \/ Q(x,y))
     ==> (forall x y. P(x,y)) \/ (forall x y. Q(x,y))|};;

  let steamroller = meson
   {%fol|((forall x. P1(x) ==> P0(x)) /\ (exists x. P1(x))) /\
     ((forall x. P2(x) ==> P0(x)) /\ (exists x. P2(x))) /\
     ((forall x. P3(x) ==> P0(x)) /\ (exists x. P3(x))) /\
     ((forall x. P4(x) ==> P0(x)) /\ (exists x. P4(x))) /\
     ((forall x. P5(x) ==> P0(x)) /\ (exists x. P5(x))) /\
     ((exists x. Q1(x)) /\ (forall x. Q1(x) ==> Q0(x))) /\
     (forall x. P0(x)
                ==> (forall y. Q0(y) ==> R(x,y)) \/
                    ((forall y. P0(y) /\ S0(y,x) /\
                                (exists z. Q0(z) /\ R(y,z))
                                ==> R(x,y)))) /\
     (forall x y. P3(y) /\ (P5(x) \/ P4(x)) ==> S0(x,y)) /\
     (forall x y. P3(x) /\ P2(y) ==> S0(x,y)) /\
     (forall x y. P2(x) /\ P1(y) ==> S0(x,y)) /\
     (forall x y. P1(x) /\ (P2(y) \/ Q1(y)) ==> ~(R(x,y))) /\
     (forall x y. P3(x) /\ P4(y) ==> R(x,y)) /\
     (forall x y. P3(x) /\ P5(y) ==> ~(R(x,y))) /\
     (forall x. (P4(x) \/ P5(x)) ==> exists y. Q0(y) /\ R(x,y))
     ==> exists x y. P0(x) /\ P0(y) /\
                     exists z. Q1(z) /\ R(y,z) /\ R(x,y)|};;

  ****************)


  (* ------------------------------------------------------------------------- *)
  (* Test it.                                                                  *)
  (* ------------------------------------------------------------------------- *)
  let prop_1 = time meson
   {%fol|p ==> q <=> ~q ==> ~p|} in
  print_fol_formula
    (prop_1);
  let prop_2 = time meson
   {%fol|~ ~p <=> p|} in
  print_fol_formula
    (prop_2);
  let prop_3 = time meson
   {%fol|~(p ==> q) ==> q ==> p|} in
  print_fol_formula
    (prop_3);
  let prop_4 = time meson
   {%fol|~p ==> q <=> ~q ==> p|} in
  print_fol_formula
    (prop_4);
  let prop_5 = time meson
   {%fol|(p \/ q ==> p \/ r) ==> p \/ (q ==> r)|} in
  print_fol_formula
    (prop_5);
  let prop_6 = time meson
   {%fol|p \/ ~p|} in
  print_fol_formula
    (prop_6);
  let prop_7 = time meson
   {%fol|p \/ ~ ~ ~p|} in
  print_fol_formula
    (prop_7);
  let prop_8 = time meson
   {%fol|((p ==> q) ==> p) ==> p|} in
  print_fol_formula
    (prop_8);
  let prop_9 = time meson
   {%fol|(p \/ q) /\ (~p \/ q) /\ (p \/ ~q) ==> ~(~q \/ ~q)|} in
  print_fol_formula
    (prop_9);
  let prop_10 = time meson
   {%fol|(q ==> r) /\ (r ==> p /\ q) /\ (p ==> q /\ r) ==> (p <=> q)|} in
  print_fol_formula
    (prop_10);
  let prop_11 = time meson
   {%fol|p <=> p|} in
  print_fol_formula
    (prop_11);
  let prop_12 = time meson
   {%fol|((p <=> q) <=> r) <=> (p <=> (q <=> r))|} in
  print_fol_formula
    (prop_12);
  let prop_13 = time meson
   {%fol|p \/ q /\ r <=> (p \/ q) /\ (p \/ r)|} in
  print_fol_formula
    (prop_13);
  let prop_14 = time meson
   {%fol|(p <=> q) <=> (q \/ ~p) /\ (~q \/ p)|} in
  print_fol_formula
    (prop_14);
  let prop_15 = time meson
   {%fol|p ==> q <=> ~p \/ q|} in
  print_fol_formula
    (prop_15);
  let prop_16 = time meson
   {%fol|(p ==> q) \/ (q ==> p)|} in
  print_fol_formula
    (prop_16);
  let prop_17 = time meson
   {%fol|p /\ (q ==> r) ==> s <=> (~p \/ q \/ s) /\ (~p \/ ~r \/ s)|} in
  print_fol_formula
    (prop_17);
  (* ------------------------------------------------------------------------- *)
  (* Monadic Predicate Logic.                                                  *)
  (* ------------------------------------------------------------------------- *)
  let p18 = time meson
   {%fol|exists y. forall x. P(y) ==> P(x)|} in
  print_fol_formula
    (p18);
  let p19 = time meson
   {%fol|exists x. forall y z. (P(y) ==> Q(z)) ==> P(x) ==> Q(x)|} in
  print_fol_formula
    (p19);
  let p20 = time meson
   {%fol|(forall x y. exists z. forall w. P(x) /\ Q(y) ==> R(z) /\ U(w)) ==>
     (exists x y. P(x) /\ Q(y)) ==>
     (exists z. R(z))|} in
  print_fol_formula
    (p20);
  let p21 = time meson
   {%fol|(exists x. P ==> Q(x)) /\ (exists x. Q(x) ==> P)
     ==> (exists x. P <=> Q(x))|} in
  print_fol_formula
    (p21);
  let p22 = time meson
   {%fol|(forall x. P <=> Q(x)) ==> (P <=> (forall x. Q(x)))|} in
  print_fol_formula
    (p22);
  let p23 = time meson
   {%fol|(forall x. P \/ Q(x)) <=> P \/ (forall x. Q(x))|} in
  print_fol_formula
    (p23);
  let p24 = time meson
   {%fol|~(exists x. U(x) /\ Q(x)) /\
     (forall x. P(x) ==> Q(x) \/ R(x)) /\
     ~(exists x. P(x) ==> (exists x. Q(x))) /\
     (forall x. Q(x) /\ R(x) ==> U(x)) ==>
     (exists x. P(x) /\ R(x))|} in
  print_fol_formula
    (p24);
  let p25 = time meson
   {%fol|(exists x. P(x)) /\
     (forall x. U(x) ==> ~G(x) /\ R(x)) /\
     (forall x. P(x) ==> G(x) /\ U(x)) /\
     ((forall x. P(x) ==> Q(x)) \/ (exists x. Q(x) /\ P(x))) ==>
     (exists x. Q(x) /\ P(x))|} in
  print_fol_formula
    (p25);
  let p26 = time meson
   {%fol|((exists x. P(x)) <=> (exists x. Q(x))) /\
     (forall x y. P(x) /\ Q(y) ==> (R(x) <=> U(y))) ==>
     ((forall x. P(x) ==> R(x)) <=> (forall x. Q(x) ==> U(x)))|} in
  print_fol_formula
    (p26);
  let p27 = time meson
   {%fol|(exists x. P(x) /\ ~Q(x)) /\
     (forall x. P(x) ==> R(x)) /\
     (forall x. U(x) /\ V(x) ==> P(x)) /\
     (exists x. R(x) /\ ~Q(x)) ==>
     (forall x. U(x) ==> ~R(x)) ==>
     (forall x. U(x) ==> ~V(x))|} in
  print_fol_formula
    (p27);
  let p28 = time meson
   {%fol|(forall x. P(x) ==> (forall x. Q(x))) /\
     ((forall x. Q(x) \/ R(x)) ==> (exists x. Q(x) /\ R(x))) /\
     ((exists x. R(x)) ==> (forall x. L(x) ==> M(x))) ==>
     (forall x. P(x) /\ L(x) ==> M(x))|} in
  print_fol_formula
    (p28);
  let p29 = time meson
   {%fol|(exists x. P(x)) /\ (exists x. G(x)) ==>
     ((forall x. P(x) ==> H(x)) /\ (forall x. G(x) ==> J(x)) <=>
      (forall x y. P(x) /\ G(y) ==> H(x) /\ J(y)))|} in
  print_fol_formula
    (p29);
  let p30 = time meson
   {%fol|(forall x. P(x) \/ G(x) ==> ~H(x)) /\ (forall x. (G(x) ==> ~U(x)) ==>
       P(x) /\ H(x)) ==>
     (forall x. U(x))|} in
  print_fol_formula
    (p30);
  let p31 = time meson
   {%fol|~(exists x. P(x) /\ (G(x) \/ H(x))) /\ (exists x. Q(x) /\ P(x)) /\
     (forall x. ~H(x) ==> J(x)) ==>
     (exists x. Q(x) /\ J(x))|} in
  print_fol_formula
    (p31);
  let p32 = time meson
   {%fol|(forall x. P(x) /\ (G(x) \/ H(x)) ==> Q(x)) /\
     (forall x. Q(x) /\ H(x) ==> J(x)) /\
     (forall x. R(x) ==> H(x)) ==>
     (forall x. P(x) /\ R(x) ==> J(x))|} in
  print_fol_formula
    (p32);
  let p33 = time meson
   {%fol|(forall x. P(a) /\ (P(x) ==> P(b)) ==> P(c)) <=>
     (forall x. P(a) ==> P(x) \/ P(c)) /\ (P(a) ==> P(b) ==> P(c))|} in
  print_fol_formula
    (p33);
  let p34 = time meson
   {%fol|((exists x. forall y. P(x) <=> P(y)) <=>
      ((exists x. Q(x)) <=> (forall y. Q(y)))) <=>
     ((exists x. forall y. Q(x) <=> Q(y)) <=>
      ((exists x. P(x)) <=> (forall y. P(y))))|} in
  print_fol_formula
    (p34);
  let p35 = time meson
   {%fol|exists x y. P(x,y) ==> (forall x y. P(x,y))|} in
  print_fol_formula
    (p35);
  (* ------------------------------------------------------------------------- *)
  (*  Full predicate logic (without Identity and Functions)                    *)
  (* ------------------------------------------------------------------------- *)
  let p36 = time meson
   {%fol|(forall x. exists y. P(x,y)) /\
     (forall x. exists y. G(x,y)) /\
     (forall x y. P(x,y) \/ G(x,y)
     ==> (forall z. P(y,z) \/ G(y,z) ==> H(x,z)))
         ==> (forall x. exists y. H(x,y))|} in
  print_fol_formula
    (p36);
  let p37 = time meson
   {%fol|(forall z.
       exists w. forall x. exists y. (P(x,z) ==> P(y,w)) /\ P(y,z) /\
       (P(y,w) ==> (exists u. Q(u,w)))) /\
     (forall x z. ~P(x,z) ==> (exists y. Q(y,z))) /\
     ((exists x y. Q(x,y)) ==> (forall x. R(x,x))) ==>
     (forall x. exists y. R(x,y))|} in
  print_fol_formula
    (p37);
  let p38 = time meson
   {%fol|(forall x.
       P(a) /\ (P(x) ==> (exists y. P(y) /\ R(x,y))) ==>
       (exists z w. P(z) /\ R(x,w) /\ R(w,z))) <=>
     (forall x.
       (~P(a) \/ P(x) \/ (exists z w. P(z) /\ R(x,w) /\ R(w,z))) /\
       (~P(a) \/ ~(exists y. P(y) /\ R(x,y)) \/
       (exists z w. P(z) /\ R(x,w) /\ R(w,z))))|} in
  print_fol_formula
    (p38);
  let p39 = time meson
   {%fol|~(exists x. forall y. P(y,x) <=> ~P(y,y))|} in
  print_fol_formula
    (p39);
  let p40 = time meson
   {%fol|(exists y. forall x. P(x,y) <=> P(x,x))
    ==> ~(forall x. exists y. forall z. P(z,y) <=> ~P(z,x))|} in
  print_fol_formula
    (p40);
  let p41 = time meson
   {%fol|(forall z. exists y. forall x. P(x,y) <=> P(x,z) /\ ~P(x,x))
    ==> ~(exists z. forall x. P(x,z))|} in
  print_fol_formula
    (p41);
  let p42 = time meson
   {%fol|~(exists y. forall x. P(x,y) <=> ~(exists z. P(x,z) /\ P(z,x)))|} in
  print_fol_formula
    (p42);
  let p43 = time meson
   {%fol|(forall x y. Q(x,y) <=> forall z. P(z,x) <=> P(z,y))
     ==> forall x y. Q(x,y) <=> Q(y,x)|} in
  print_fol_formula
    (p43);
  let p44 = time meson
   {%fol|(forall x. P(x) ==> (exists y. G(y) /\ H(x,y)) /\
     (exists y. G(y) /\ ~H(x,y))) /\
     (exists x. J(x) /\ (forall y. G(y) ==> H(x,y))) ==>
     (exists x. J(x) /\ ~P(x))|} in
  print_fol_formula
    (p44);
  let p45 = time meson
   {%fol|(forall x.
       P(x) /\ (forall y. G(y) /\ H(x,y) ==> J(x,y)) ==>
         (forall y. G(y) /\ H(x,y) ==> R(y))) /\
     ~(exists y. L(y) /\ R(y)) /\
     (exists x. P(x) /\ (forall y. H(x,y) ==>
       L(y)) /\ (forall y. G(y) /\ H(x,y) ==> J(x,y))) ==>
     (exists x. P(x) /\ ~(exists y. G(y) /\ H(x,y)))|} in
  print_fol_formula
    (p45);
  let p46 = time meson
   {%fol|(forall x. P(x) /\ (forall y. P(y) /\ H(y,x) ==> G(y)) ==> G(x)) /\
     ((exists x. P(x) /\ ~G(x)) ==>
      (exists x. P(x) /\ ~G(x) /\
                 (forall y. P(y) /\ ~G(y) ==> J(x,y)))) /\
     (forall x y. P(x) /\ P(y) /\ H(x,y) ==> ~J(y,x)) ==>
     (forall x. P(x) ==> G(x))|} in
  print_fol_formula
    (p46);
  (* ------------------------------------------------------------------------- *)
  (* Example from Manthey and Bry, CADE-9.                                     *)
  (* ------------------------------------------------------------------------- *)
  let p55 = time meson
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
  print_fol_formula
    (p55);
  let p57 = time meson
   {%fol|P(f((a),b),f(b,c)) /\
    P(f(b,c),f(a,c)) /\
    (forall (x) y z. P(x,y) /\ P(y,z) ==> P(x,z))
    ==> P(f(a,b),f(a,c))|} in
  print_fol_formula
    (p57);
  (* ------------------------------------------------------------------------- *)
  (* See info-hol, circa 1500.                                                 *)
  (* ------------------------------------------------------------------------- *)
  let p58 = time meson
   {%fol|forall P Q R. forall x. exists v. exists w. forall y. forall z.
      ((P(x) /\ Q(y)) ==> ((P(v) \/ R(w))  /\ (R(z) ==> Q(v))))|} in
  print_fol_formula
    (p58);
  let p59 = time meson
   {%fol|(forall x. P(x) <=> ~P(f(x))) ==> (exists x. P(x) /\ ~P(f(x)))|} in
  print_fol_formula
    (p59);
  let p60 = time meson
   {%fol|forall x. P(x,f(x)) <=>
              exists y. (forall z. P(z,y) ==> P(z,f(x))) /\ P(x,y)|} in
  print_fol_formula
    (p60);
  (* ------------------------------------------------------------------------- *)
  (* From Gilmore's classic paper.                                             *)
  (* ------------------------------------------------------------------------- *)

  (*** Amazingly, this still seems non-trivial... in HOL it works at depth 45!

  let gilmore_1 = time meson
   {%fol|exists x. forall y z.
        ((F(y) ==> G(y)) <=> F(x)) /\
        ((F(y) ==> H(y)) <=> G(x)) /\
        (((F(y) ==> G(y)) ==> H(y)) <=> H(x))
        ==> F(z) /\ G(z) /\ H(z)|};;

   ***)

  (*** This is not valid, according to Gilmore

  let gilmore_2 = time meson
   {%fol|exists x y. forall z.
          (F(x,z) <=> F(z,y)) /\ (F(z,y) <=> F(z,z)) /\ (F(x,y) <=> F(y,x))
          ==> (F(x,y) <=> F(x,z))|};;

   ***)
  let gilmore_3 = time meson
   {%fol|exists x. forall y z.
          ((F(y,z) ==> (G(y) ==> H(x))) ==> F(x,x)) /\
          ((F(z,x) ==> G(x)) ==> H(z)) /\
          F(x,y)
          ==> F(z,z)|} in
  print_fol_formula
    (gilmore_3);
  let gilmore_4 = time meson
   {%fol|exists x y. forall z.
          (F(x,y) ==> F(y,z) /\ F(z,z)) /\
          (F(x,y) /\ G(x,y) ==> G(x,z) /\ G(z,z))|} in
  print_fol_formula
    (gilmore_4);
  let gilmore_5 = time meson
   {%fol|(forall x. exists y. F(x,y) \/ F(y,x)) /\
     (forall x y. F(y,x) ==> F(y,y))
     ==> exists z. F(z,z)|} in
  print_fol_formula
    (gilmore_5);
  let gilmore_6 = time meson
   {%fol|forall x. exists y.
          (exists u. forall v. F(u,x) ==> G(v,u) /\ G(u,x))
          ==> (exists u. forall v. F(u,y) ==> G(v,u) /\ G(u,y)) \/
              (forall u v. exists w. G(v,u) \/ H(w,y,u) ==> G(u,w))|} in
  print_fol_formula
    (gilmore_6);
  let gilmore_7 = time meson
   {%fol|(forall x. K(x) ==> exists y. L(y) /\ (F(x,y) ==> G(x,y))) /\
     (exists z. K(z) /\ forall u. L(u) ==> F(z,u))
     ==> exists v w. K(v) /\ L(w) /\ G(v,w)|} in
  print_fol_formula
    (gilmore_7);
  let gilmore_8 = time meson
   {%fol|exists x. forall y z.
          ((F(y,z) ==> (G(y) ==> (forall u. exists v. H(u,v,x)))) ==> F(x,x)) /\
          ((F(z,x) ==> G(x)) ==> (forall u. exists v. H(u,v,z))) /\
          F(x,y)
          ==> F(z,z)|} in
  print_fol_formula
    (gilmore_8);
  (*** This is still a very hard problem

  let gilmore_9 = time meson
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
  (* Translation of Gilmore procedure using separate definitions.              *)
  (* ------------------------------------------------------------------------- *)
  let gilmore_9a = time meson
   {%fol|(forall x y. P(x,y) <=>
                  forall u. exists v. F(x,u,v) /\ G(y,u) /\ ~H(x,y))
     ==> forall x. exists y. forall z.
               (P(y,x) ==> (P(x,z) ==> P(x,y))) /\
               (P(x,y) ==> (~P(x,z) ==> P(y,x) /\ P(z,y)))|} in
  print_fol_formula
    (gilmore_9a);
  (* ------------------------------------------------------------------------- *)
  (* Example from Davis-Putnam papers where Gilmore procedure is poor.         *)
  (* ------------------------------------------------------------------------- *)
  let davis_putnam_example = time meson
   {%fol|exists x. exists y. forall z.
          (F(x,y) ==> (F(y,z) /\ F(z,z))) /\
          ((F(x,y) /\ G(x,y)) ==> (G(x,z) /\ G(z,z)))|} in
  print_fol_formula
    (davis_putnam_example);
  (* ------------------------------------------------------------------------- *)
  (* The "connections make things worse" example once again.                   *)
  (* ------------------------------------------------------------------------- *)
  print_fol_formula
    (meson {%fol|~p /\ (p \/ q) /\ (r \/ s) /\ (~q \/ t \/ u) /\
            (~r \/ ~t) /\ (~r \/ ~u) /\ (~q \/ v \/ w) /\
            (~s \/ ~v) /\ (~s \/ ~w) ==> false|});
  [%expect {| |}]
;;
