open Lib
open Formulas
open Prop
open Fol
open Skolem
open Herbrand
open Unif

(* Warnings the book's style trips in this file; the rest of the
   library compiles with them on.  See lib/dune. *)
[@@@warning "-10"]

(* ========================================================================= *)
(* Tableaux, seen as an optimized version of a Prawitz-like procedure.       *)
(*                                                                           *)
(* Copyright (c) 2003-2007, John Harrison. (See "LICENSE.txt" for details.)  *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Unify literals (just pretend the toplevel relation is a function).        *)
(* ------------------------------------------------------------------------- *)

let rec unify_literals env tmp =
  match tmp with
    Atom(R(p1,a1)),Atom(R(p2,a2)) -> unify env [Fn(p1,a1),Fn(p2,a2)]
  | Not(p),Not(q) -> unify_literals env (p,q)
  | False,False -> env
  | _ -> failwith "Can't unify literals";;

(* ------------------------------------------------------------------------- *)
(* Unify complementary literals.                                             *)
(* ------------------------------------------------------------------------- *)

let unify_complements env (p,q) = unify_literals env (p,negate q);;

(* ------------------------------------------------------------------------- *)
(* Unify and refute a set of disjuncts.                                      *)
(* ------------------------------------------------------------------------- *)

let rec unify_refute djs env =
  match djs with
    [] -> env
  | d::odjs -> let pos,neg = partition positive d in
               tryfind (unify_refute odjs ** unify_complements env)
                       (allpairs (fun p q -> (p,q)) pos neg);;

(* ------------------------------------------------------------------------- *)
(* Hence a Prawitz-like procedure (using unification on DNF).                *)
(* ------------------------------------------------------------------------- *)

let rec prawitz_loop djs0 fvs djs n =
  let l = length fvs in
  let newvars = map (fun k -> "_"^string_of_int (n * l + k)) (1--l) in
  let inst = fpf fvs (map (fun x -> Var x) newvars) in
  let djs1 = distrib (image (image (subst inst)) djs0) djs in
  try unify_refute djs1 undefined,(n + 1)
  with Failure _ -> prawitz_loop djs0 fvs djs1 (n + 1);;

let prawitz fm =
  let fm0 = skolemize(Not(generalize fm)) in
  snd(prawitz_loop (simpdnf fm0) (fv fm0) [[]] 0);;

let%expect_test "eg: Examples" =
  let p20 = prawitz
   {%fol|(forall x y. exists z. forall w. P(x) /\ Q(y) ==> R(z) /\ U(w))
     ==> (exists x y. P(x) /\ Q(y)) ==> (exists z. R(z))|} in
  print_int
    (p20);
  [%expect {| 2 |}]
;;

(* ------------------------------------------------------------------------- *)
(* Comparison of number of ground instances.                                 *)
(* ------------------------------------------------------------------------- *)

let compare fm =
  prawitz fm,davisputnam fm;;


let%expect_test _ =
  let p19 = compare
   {%fol|exists x. forall y z. (P(y) ==> Q(z)) ==> P(x) ==> Q(x)|} in
  print_pair print_int print_int
    (p19);
  let p20 = compare
   {%fol|(forall x y. exists z. forall w. P(x) /\ Q(y) ==> R(z) /\ U(w))
     ==> (exists x y. P(x) /\ Q(y)) ==> (exists z. R(z))|} in
  print_pair print_int print_int
    (p20);
  let p24 = compare
   {%fol|~(exists x. U(x) /\ Q(x)) /\
     (forall x. P(x) ==> Q(x) \/ R(x)) /\
     ~(exists x. P(x) ==> (exists x. Q(x))) /\
     (forall x. Q(x) /\ R(x) ==> U(x))
     ==> (exists x. P(x) /\ R(x))|} in
  print_pair print_int print_int
    (p24);
  let p39 = compare
   {%fol|~(exists x. forall y. P(y,x) <=> ~P(y,y))|} in
  print_pair print_int print_int
    (p39);
  let p42 = compare
   {%fol|~(exists y. forall x. P(x,y) <=> ~(exists z. P(x,z) /\ P(z,x)))|} in
  print_pair print_int print_int
    (p42);
  (***** Too slow?

  let p43 = compare
   {%fol|(forall x y. Q(x,y) <=> forall z. P(z,x) <=> P(z,y))
     ==> forall x y. Q(x,y) <=> Q(y,x)|};;

   ******)
  let p44 = compare
   {%fol|(forall x. P(x) ==> (exists y. G(y) /\ H(x,y)) /\
     (exists y. G(y) /\ ~H(x,y))) /\
     (exists x. J(x) /\ (forall y. G(y) ==> H(x,y)))
     ==> (exists x. J(x) /\ ~P(x))|} in
  print_pair print_int print_int
    (p44);
  let p59 = compare
   {%fol|(forall x. P(x) <=> ~P(f(x))) ==> (exists x. P(x) /\ ~P(f(x)))|} in
  print_pair print_int print_int
    (p59);
  let p60 = compare
   {%fol|forall x. P(x,f(x)) <=>
               exists y. (forall z. P(z,y) ==> P(z,f(x))) /\ P(x,y)|} in
  print_pair print_int print_int
    (p60);
  [%expect {|
    0 ground instances tried; 0 items in list
    0 ground instances tried; 0 items in list
    1 ground instances tried; 3 items in list
    1 ground instances tried; 3 items in list
    2 ground instances tried; 6 items in list
    (3, 3)0 ground instances tried; 0 items in list
    0 ground instances tried; 0 items in list
    1 ground instances tried; 5 items in list
    2 ground instances tried; 7 items in list
    3 ground instances tried; 10 items in list
    4 ground instances tried; 12 items in list
    5 ground instances tried; 13 items in list
    6 ground instances tried; 14 items in list
    7 ground instances tried; 15 items in list
    8 ground instances tried; 16 items in list
    8 ground instances tried; 16 items in list
    9 ground instances tried; 18 items in list
    10 ground instances tried; 20 items in list
    11 ground instances tried; 22 items in list
    12 ground instances tried; 24 items in list
    13 ground instances tried; 26 items in list
    14 ground instances tried; 28 items in list
    15 ground instances tried; 30 items in list
    16 ground instances tried; 32 items in list
    17 ground instances tried; 35 items in list
    18 ground instances tried; 37 items in list
    (2, 19)0 ground instances tried; 0 items in list
    0 ground instances tried; 0 items in list
    (1, 1)0 ground instances tried; 0 items in list
    0 ground instances tried; 0 items in list
    (1, 1)0 ground instances tried; 0 items in list
    0 ground instances tried; 0 items in list
    1 ground instances tried; 5 items in list
    1 ground instances tried; 5 items in list
    2 ground instances tried; 8 items in list
    (2, 3)0 ground instances tried; 0 items in list
    0 ground instances tried; 0 items in list
    1 ground instances tried; 7 items in list
    1 ground instances tried; 7 items in list
    2 ground instances tried; 13 items in list
    (2, 3)0 ground instances tried; 0 items in list
    0 ground instances tried; 0 items in list
    1 ground instances tried; 3 items in list
    1 ground instances tried; 3 items in list
    (2, 2)0 ground instances tried; 0 items in list
    0 ground instances tried; 0 items in list
    1 ground instances tried; 8 items in list
    2 ground instances tried; 11 items in list
    3 ground instances tried; 17 items in list
    4 ground instances tried; 19 items in list
    4 ground instances tried; 19 items in list
    5 ground instances tried; 22 items in list
    6 ground instances tried; 25 items in list
    7 ground instances tried; 28 items in list
    8 ground instances tried; 31 items in list
    9 ground instances tried; 33 items in list
    10 ground instances tried; 35 items in list
    11 ground instances tried; 37 items in list
    12 ground instances tried; 39 items in list
    (1, 13)
    |}]
;;

(* ------------------------------------------------------------------------- *)
(* More standard tableau procedure, effectively doing DNF incrementally.     *)
(* ------------------------------------------------------------------------- *)

let rec tableau (fms,lits,n) cont (env,k) =
  if n < 0 then failwith "no proof at this level" else
  match fms with
    [] -> failwith "tableau: no proof"
  | And(p,q)::unexp ->
      tableau (p::q::unexp,lits,n) cont (env,k)
  | Or(p,q)::unexp ->
      tableau (p::unexp,lits,n) (tableau (q::unexp,lits,n) cont) (env,k)
  | Forall(x,p)::unexp ->
      let y = Var("_" ^ string_of_int k) in
      let p' = subst (x |=> y) p in
      tableau (p'::unexp@[Forall(x,p)],lits,n-1) cont (env,k+1)
  | fm::unexp ->
      try tryfind (fun l -> cont(unify_complements env (fm,l),k)) lits
      with Failure _ -> tableau (unexp,fm::lits,n) cont (env,k);;

let deepen f n =
  let rec deepen1 f n =
    try print_string "Searching with depth limit ";
      print_int n;
      flush stdout;
      f n
    with Failure _ ->
      print_string("\r");
      flush stdout;
      deepen1 f (n + 1) in
  let v = deepen1 f n in
  print_newline();
  v;;

let tabrefute fms =
  deepen (fun n -> tableau (fms,[],n) (fun x -> x) (undefined,0); n) 0;;

let tab fm =
  let sfm = askolemize(Not(generalize fm)) in
  if sfm = False then 0 else tabrefute [sfm];;

let%expect_test "eg" =
  let p38 = tab
   {%fol|(forall x.
       P(a) /\ (P(x) ==> (exists y. P(y) /\ R(x,y))) ==>
       (exists z w. P(z) /\ R(x,w) /\ R(w,z))) <=>
     (forall x.
       (~P(a) \/ P(x) \/ (exists z w. P(z) /\ R(x,w) /\ R(w,z))) /\
       (~P(a) \/ ~(exists y. P(y) /\ R(x,y)) \/
       (exists z w. P(z) /\ R(x,w) /\ R(w,z))))|} in
  print_int
    (p38);
  [%expect {|
    Searching with depth limit 0Searching with depth limit 1Searching with depth limit 2Searching with depth limit 3Searching with depth limit 4
    4
    |}]
;;


(* ------------------------------------------------------------------------- *)
(* Try to split up the initial formula first; often a big improvement.       *)
(* ------------------------------------------------------------------------- *)

let splittab fm = 
  map tabrefute (simpdnf(askolemize(Not(generalize fm))));;

let%expect_test "eg: the Andrews challenge" =
  let p34 = splittab
   {%fol|((exists x. forall y. P(x) <=> P(y)) <=>
      ((exists x. Q(x)) <=> (forall y. Q(y)))) <=>
     ((exists x. forall y. Q(x) <=> Q(y)) <=>
      ((exists x. P(x)) <=> (forall y. P(y))))|} in
  print_list print_int
    (p34);
  (* ------------------------------------------------------------------------- *)
  (* Another nice example from EWD 1602.                                       *)
  (* ------------------------------------------------------------------------- *)
  let ewd1062 = splittab
   {%fol|(forall x. x <= x) /\
     (forall x y z. x <= y /\ y <= z ==> x <= z) /\
     (forall x y. f(x) <= y <=> x <= g(y))
     ==> (forall x y. x <= y ==> f(x) <= f(y)) /\
         (forall x y. x <= y ==> g(x) <= g(y))|} in
  print_list print_int
    (ewd1062);
  [%expect {|
    Searching with depth limit 0Searching with depth limit 1Searching with depth limit 2Searching with depth limit 3Searching with depth limit 4Searching with depth limit 5
    Searching with depth limit 0Searching with depth limit 1Searching with depth limit 2Searching with depth limit 3Searching with depth limit 4
    Searching with depth limit 0Searching with depth limit 1Searching with depth limit 2Searching with depth limit 3Searching with depth limit 4Searching with depth limit 5
    Searching with depth limit 0Searching with depth limit 1Searching with depth limit 2Searching with depth limit 3
    Searching with depth limit 0Searching with depth limit 1Searching with depth limit 2Searching with depth limit 3
    Searching with depth limit 0Searching with depth limit 1Searching with depth limit 2Searching with depth limit 3
    Searching with depth limit 0Searching with depth limit 1Searching with depth limit 2
    Searching with depth limit 0Searching with depth limit 1Searching with depth limit 2Searching with depth limit 3Searching with depth limit 4
    Searching with depth limit 0Searching with depth limit 1Searching with depth limit 2Searching with depth limit 3Searching with depth limit 4Searching with depth limit 5Searching with depth limit 6
    Searching with depth limit 0Searching with depth limit 1Searching with depth limit 2
    Searching with depth limit 0Searching with depth limit 1Searching with depth limit 2Searching with depth limit 3
    Searching with depth limit 0Searching with depth limit 1Searching with depth limit 2Searching with depth limit 3
    Searching with depth limit 0Searching with depth limit 1Searching with depth limit 2Searching with depth limit 3Searching with depth limit 4
    Searching with depth limit 0Searching with depth limit 1Searching with depth limit 2Searching with depth limit 3
    Searching with depth limit 0Searching with depth limit 1Searching with depth limit 2Searching with depth limit 3
    Searching with depth limit 0Searching with depth limit 1Searching with depth limit 2Searching with depth limit 3
    Searching with depth limit 0Searching with depth limit 1Searching with depth limit 2Searching with depth limit 3
    Searching with depth limit 0Searching with depth limit 1Searching with depth limit 2
    Searching with depth limit 0Searching with depth limit 1Searching with depth limit 2
    Searching with depth limit 0Searching with depth limit 1Searching with depth limit 2Searching with depth limit 3
    Searching with depth limit 0Searching with depth limit 1Searching with depth limit 2Searching with depth limit 3Searching with depth limit 4Searching with depth limit 5Searching with depth limit 6
    Searching with depth limit 0Searching with depth limit 1Searching with depth limit 2Searching with depth limit 3
    Searching with depth limit 0Searching with depth limit 1Searching with depth limit 2
    Searching with depth limit 0Searching with depth limit 1Searching with depth limit 2Searching with depth limit 3Searching with depth limit 4
    Searching with depth limit 0Searching with depth limit 1Searching with depth limit 2Searching with depth limit 3
    Searching with depth limit 0Searching with depth limit 1Searching with depth limit 2Searching with depth limit 3
    Searching with depth limit 0Searching with depth limit 1Searching with depth limit 2Searching with depth limit 3
    Searching with depth limit 0Searching with depth limit 1Searching with depth limit 2Searching with depth limit 3
    Searching with depth limit 0Searching with depth limit 1Searching with depth limit 2Searching with depth limit 3
    Searching with depth limit 0Searching with depth limit 1Searching with depth limit 2Searching with depth limit 3Searching with depth limit 4
    Searching with depth limit 0Searching with depth limit 1Searching with depth limit 2Searching with depth limit 3Searching with depth limit 4
    Searching with depth limit 0Searching with depth limit 1Searching with depth limit 2Searching with depth limit 3Searching with depth limit 4
    [5; 4; 5; 3; 3; 3; 2; 4; 6; 2; 3; 3; 4; 3; 3; 3; 3; 2; 2; 3; 6; 3; 2; 4; 3; 3; 3; 3; 3; 4; 4; 4]Searching with depth limit 0Searching with depth limit 1Searching with depth limit 2Searching with depth limit 3Searching with depth limit 4Searching with depth limit 5Searching with depth limit 6Searching with depth limit 7Searching with depth limit 8Searching with depth limit 9
    Searching with depth limit 0Searching with depth limit 1Searching with depth limit 2Searching with depth limit 3Searching with depth limit 4Searching with depth limit 5Searching with depth limit 6Searching with depth limit 7Searching with depth limit 8Searching with depth limit 9
    [9; 9]
    |}]
;;


(* ------------------------------------------------------------------------- *)
(* Do all the equality-free Pelletier problems, and more, as examples.       *)
(* ------------------------------------------------------------------------- *)

(***********

let p1 = time splittab
 {%fol|p ==> q <=> ~q ==> ~p|};;

let p2 = time splittab
 {%fol|~ ~p <=> p|};;

let p3 = time splittab
 {%fol|~(p ==> q) ==> q ==> p|};;

let p4 = time splittab
 {%fol|~p ==> q <=> ~q ==> p|};;

let p5 = time splittab
 {%fol|(p \/ q ==> p \/ r) ==> p \/ (q ==> r)|};;

let p6 = time splittab
 {%fol|p \/ ~p|};;

let p7 = time splittab
 {%fol|p \/ ~ ~ ~p|};;

let p8 = time splittab
 {%fol|((p ==> q) ==> p) ==> p|};;

let p9 = time splittab
 {%fol|(p \/ q) /\ (~p \/ q) /\ (p \/ ~q) ==> ~(~q \/ ~q)|};;

let p10 = time splittab
 {%fol|(q ==> r) /\ (r ==> p /\ q) /\ (p ==> q /\ r) ==> (p <=> q)|};;

let p11 = time splittab
 {%fol|p <=> p|};;

let p12 = time splittab
 {%fol|((p <=> q) <=> r) <=> (p <=> (q <=> r))|};;

let p13 = time splittab
 {%fol|p \/ q /\ r <=> (p \/ q) /\ (p \/ r)|};;

let p14 = time splittab
 {%fol|(p <=> q) <=> (q \/ ~p) /\ (~q \/ p)|};;

let p15 = time splittab
 {%fol|p ==> q <=> ~p \/ q|};;

let p16 = time splittab
 {%fol|(p ==> q) \/ (q ==> p)|};;

let p17 = time splittab
 {%fol|p /\ (q ==> r) ==> s <=> (~p \/ q \/ s) /\ (~p \/ ~r \/ s)|};;

(* ------------------------------------------------------------------------- *)
(* Pelletier problems: monadic predicate logic.                              *)
(* ------------------------------------------------------------------------- *)

let p18 = time splittab
 {%fol|exists y. forall x. P(y) ==> P(x)|};;

let p19 = time splittab
 {%fol|exists x. forall y z. (P(y) ==> Q(z)) ==> P(x) ==> Q(x)|};;

let p20 = time splittab
 {%fol|(forall x y. exists z. forall w. P(x) /\ Q(y) ==> R(z) /\ U(w))
   ==> (exists x y. P(x) /\ Q(y)) ==> (exists z. R(z))|};;

let p21 = time splittab
 {%fol|(exists x. P ==> Q(x)) /\ (exists x. Q(x) ==> P)
   ==> (exists x. P <=> Q(x))|};;

let p22 = time splittab
 {%fol|(forall x. P <=> Q(x)) ==> (P <=> (forall x. Q(x)))|};;

let p23 = time splittab
 {%fol|(forall x. P \/ Q(x)) <=> P \/ (forall x. Q(x))|};;

let p24 = time splittab
 {%fol|~(exists x. U(x) /\ Q(x)) /\
   (forall x. P(x) ==> Q(x) \/ R(x)) /\
   ~(exists x. P(x) ==> (exists x. Q(x))) /\
   (forall x. Q(x) /\ R(x) ==> U(x)) ==>
   (exists x. P(x) /\ R(x))|};;

let p25 = time splittab
 {%fol|(exists x. P(x)) /\
   (forall x. U(x) ==> ~G(x) /\ R(x)) /\
   (forall x. P(x) ==> G(x) /\ U(x)) /\
   ((forall x. P(x) ==> Q(x)) \/ (exists x. Q(x) /\ P(x)))
   ==> (exists x. Q(x) /\ P(x))|};;

let p26 = time splittab
 {%fol|((exists x. P(x)) <=> (exists x. Q(x))) /\
   (forall x y. P(x) /\ Q(y) ==> (R(x) <=> U(y)))
   ==> ((forall x. P(x) ==> R(x)) <=> (forall x. Q(x) ==> U(x)))|};;

let p27 = time splittab
 {%fol|(exists x. P(x) /\ ~Q(x)) /\
   (forall x. P(x) ==> R(x)) /\
   (forall x. U(x) /\ V(x) ==> P(x)) /\
   (exists x. R(x) /\ ~Q(x))
   ==> (forall x. U(x) ==> ~R(x))
       ==> (forall x. U(x) ==> ~V(x))|};;

let p28 = time splittab
 {%fol|(forall x. P(x) ==> (forall x. Q(x))) /\
   ((forall x. Q(x) \/ R(x)) ==> (exists x. Q(x) /\ R(x))) /\
   ((exists x. R(x)) ==> (forall x. L(x) ==> M(x))) ==>
   (forall x. P(x) /\ L(x) ==> M(x))|};;

let p29 = time splittab
 {%fol|(exists x. P(x)) /\ (exists x. G(x)) ==>
   ((forall x. P(x) ==> H(x)) /\ (forall x. G(x) ==> J(x)) <=>
    (forall x y. P(x) /\ G(y) ==> H(x) /\ J(y)))|};;

let p30 = time splittab
 {%fol|(forall x. P(x) \/ G(x) ==> ~H(x)) /\
   (forall x. (G(x) ==> ~U(x)) ==> P(x) /\ H(x))
   ==> (forall x. U(x))|};;

let p31 = time splittab
 {%fol|~(exists x. P(x) /\ (G(x) \/ H(x))) /\
   (exists x. Q(x) /\ P(x)) /\
   (forall x. ~H(x) ==> J(x))
   ==> (exists x. Q(x) /\ J(x))|};;

let p32 = time splittab
 {%fol|(forall x. P(x) /\ (G(x) \/ H(x)) ==> Q(x)) /\
   (forall x. Q(x) /\ H(x) ==> J(x)) /\
   (forall x. R(x) ==> H(x))
   ==> (forall x. P(x) /\ R(x) ==> J(x))|};;

let p33 = time splittab
 {%fol|(forall x. P(a) /\ (P(x) ==> P(b)) ==> P(c)) <=>
   (forall x. P(a) ==> P(x) \/ P(c)) /\ (P(a) ==> P(b) ==> P(c))|};;

let p34 = time splittab
 {%fol|((exists x. forall y. P(x) <=> P(y)) <=>
    ((exists x. Q(x)) <=> (forall y. Q(y)))) <=>
   ((exists x. forall y. Q(x) <=> Q(y)) <=>
    ((exists x. P(x)) <=> (forall y. P(y))))|};;

let p35 = time splittab
 {%fol|exists x y. P(x,y) ==> (forall x y. P(x,y))|};;

(* ------------------------------------------------------------------------- *)
(* Full predicate logic (without identity and functions).                    *)
(* ------------------------------------------------------------------------- *)

let p36 = time splittab
 {%fol|(forall x. exists y. P(x,y)) /\
   (forall x. exists y. G(x,y)) /\
   (forall x y. P(x,y) \/ G(x,y)
   ==> (forall z. P(y,z) \/ G(y,z) ==> H(x,z)))
       ==> (forall x. exists y. H(x,y))|};;

let p37 = time splittab
 {%fol|(forall z.
     exists w. forall x. exists y. (P(x,z) ==> P(y,w)) /\ P(y,z) /\
     (P(y,w) ==> (exists u. Q(u,w)))) /\
   (forall x z. ~P(x,z) ==> (exists y. Q(y,z))) /\
   ((exists x y. Q(x,y)) ==> (forall x. R(x,x))) ==>
   (forall x. exists y. R(x,y))|};;

let p38 = time splittab
 {%fol|(forall x.
     P(a) /\ (P(x) ==> (exists y. P(y) /\ R(x,y))) ==>
     (exists z w. P(z) /\ R(x,w) /\ R(w,z))) <=>
   (forall x.
     (~P(a) \/ P(x) \/ (exists z w. P(z) /\ R(x,w) /\ R(w,z))) /\
     (~P(a) \/ ~(exists y. P(y) /\ R(x,y)) \/
     (exists z w. P(z) /\ R(x,w) /\ R(w,z))))|};;

let p39 = time splittab
 {%fol|~(exists x. forall y. P(y,x) <=> ~P(y,y))|};;

let p40 = time splittab
 {%fol|(exists y. forall x. P(x,y) <=> P(x,x))
  ==> ~(forall x. exists y. forall z. P(z,y) <=> ~P(z,x))|};;

let p41 = time splittab
 {%fol|(forall z. exists y. forall x. P(x,y) <=> P(x,z) /\ ~P(x,x))
  ==> ~(exists z. forall x. P(x,z))|};;

let p42 = time splittab
 {%fol|~(exists y. forall x. P(x,y) <=> ~(exists z. P(x,z) /\ P(z,x)))|};;

let p43 = time splittab
 {%fol|(forall x y. Q(x,y) <=> forall z. P(z,x) <=> P(z,y))
   ==> forall x y. Q(x,y) <=> Q(y,x)|};;

let p44 = time splittab
 {%fol|(forall x. P(x) ==> (exists y. G(y) /\ H(x,y)) /\
   (exists y. G(y) /\ ~H(x,y))) /\
   (exists x. J(x) /\ (forall y. G(y) ==> H(x,y))) ==>
   (exists x. J(x) /\ ~P(x))|};;

let p45 = time splittab
 {%fol|(forall x.
     P(x) /\ (forall y. G(y) /\ H(x,y) ==> J(x,y)) ==>
       (forall y. G(y) /\ H(x,y) ==> R(y))) /\
   ~(exists y. L(y) /\ R(y)) /\
   (exists x. P(x) /\ (forall y. H(x,y) ==>
     L(y)) /\ (forall y. G(y) /\ H(x,y) ==> J(x,y))) ==>
   (exists x. P(x) /\ ~(exists y. G(y) /\ H(x,y)))|};;

let p46 = time splittab
 {%fol|(forall x. P(x) /\ (forall y. P(y) /\ H(y,x) ==> G(y)) ==> G(x)) /\
   ((exists x. P(x) /\ ~G(x)) ==>
    (exists x. P(x) /\ ~G(x) /\
               (forall y. P(y) /\ ~G(y) ==> J(x,y)))) /\
   (forall x y. P(x) /\ P(y) /\ H(x,y) ==> ~J(y,x)) ==>
   (forall x. P(x) ==> G(x))|};;

(* ------------------------------------------------------------------------- *)
(* Well-known "Agatha" example; cf. Manthey and Bry, CADE-9.                 *)
(* ------------------------------------------------------------------------- *)

let p55 = time splittab
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

let p57 = time splittab
 {%fol|P(f((a),b),f(b,c)) /\
   P(f(b,c),f(a,c)) /\
   (forall (x) y z. P(x,y) /\ P(y,z) ==> P(x,z))
   ==> P(f(a,b),f(a,c))|};;

(* ------------------------------------------------------------------------- *)
(* See info-hol, circa 1500.                                                 *)
(* ------------------------------------------------------------------------- *)

let p58 = time splittab
 {%fol|forall P Q R. forall x. exists v. exists w. forall y. forall z.
    ((P(x) /\ Q(y)) ==> ((P(v) \/ R(w))  /\ (R(z) ==> Q(v))))|};;

let p59 = time splittab
 {%fol|(forall x. P(x) <=> ~P(f(x))) ==> (exists x. P(x) /\ ~P(f(x)))|};;

let p60 = time splittab
 {%fol|forall x. P(x,f(x)) <=>
            exists y. (forall z. P(z,y) ==> P(z,f(x))) /\ P(x,y)|};;

(* ------------------------------------------------------------------------- *)
(* From Gilmore's classic paper.                                             *)
(* ------------------------------------------------------------------------- *)

(***** This is still too hard for us! Amazing...

let gilmore_1 = time splittab
 {%fol|exists x. forall y z.
      ((F(y) ==> G(y)) <=> F(x)) /\
      ((F(y) ==> H(y)) <=> G(x)) /\
      (((F(y) ==> G(y)) ==> H(y)) <=> H(x))
      ==> F(z) /\ G(z) /\ H(z)|};;

 ******)

(*** This is not valid, according to Gilmore

let gilmore_2 = time splittab
 {%fol|exists x y. forall z.
        (F(x,z) <=> F(z,y)) /\ (F(z,y) <=> F(z,z)) /\ (F(x,y) <=> F(y,x))
        ==> (F(x,y) <=> F(x,z))|};;

 ***)

let gilmore_3 = time splittab
 {%fol|exists x. forall y z.
        ((F(y,z) ==> (G(y) ==> H(x))) ==> F(x,x)) /\
        ((F(z,x) ==> G(x)) ==> H(z)) /\
        F(x,y)
        ==> F(z,z)|};;

let gilmore_4 = time splittab
 {%fol|exists x y. forall z.
        (F(x,y) ==> F(y,z) /\ F(z,z)) /\
        (F(x,y) /\ G(x,y) ==> G(x,z) /\ G(z,z))|};;

let gilmore_5 = time splittab
 {%fol|(forall x. exists y. F(x,y) \/ F(y,x)) /\
   (forall x y. F(y,x) ==> F(y,y))
   ==> exists z. F(z,z)|};;

let gilmore_6 = time splittab
 {%fol|forall x. exists y.
        (exists u. forall v. F(u,x) ==> G(v,u) /\ G(u,x))
        ==> (exists u. forall v. F(u,y) ==> G(v,u) /\ G(u,y)) \/
            (forall u v. exists w. G(v,u) \/ H(w,y,u) ==> G(u,w))|};;

let gilmore_7 = time splittab
 {%fol|(forall x. K(x) ==> exists y. L(y) /\ (F(x,y) ==> G(x,y))) /\
   (exists z. K(z) /\ forall u. L(u) ==> F(z,u))
   ==> exists v w. K(v) /\ L(w) /\ G(v,w)|};;

let gilmore_8 = time splittab
 {%fol|exists x. forall y z.
        ((F(y,z) ==> (G(y) ==> (forall u. exists v. H(u,v,x)))) ==> F(x,x)) /\
        ((F(z,x) ==> G(x)) ==> (forall u. exists v. H(u,v,z))) /\
        F(x,y)
        ==> F(z,z)|};;

let gilmore_9 = time splittab
 {%fol|forall x. exists y. forall z.
        ((forall u. exists v. F(y,u,v) /\ G(y,u) /\ ~H(y,x))
          ==> (forall u. exists v. F(x,u,v) /\ G(z,u) /\ ~H(x,z))
          ==> (forall u. exists v. F(x,u,v) /\ G(y,u) /\ ~H(x,y))) /\
        ((forall u. exists v. F(x,u,v) /\ G(y,u) /\ ~H(x,y))
         ==> ~(forall u. exists v. F(x,u,v) /\ G(z,u) /\ ~H(x,z))
         ==> (forall u. exists v. F(y,u,v) /\ G(y,u) /\ ~H(y,x)) /\
             (forall u. exists v. F(z,u,v) /\ G(y,u) /\ ~H(z,y)))|};;

(* ------------------------------------------------------------------------- *)
(* Example from Davis-Putnam papers where Gilmore procedure is poor.         *)
(* ------------------------------------------------------------------------- *)

let davis_putnam_example = time splittab
 {%fol|exists x. exists y. forall z.
        (F(x,y) ==> (F(y,z) /\ F(z,z))) /\
        ((F(x,y) /\ G(x,y)) ==> (G(x,z) /\ G(z,z)))|};;

*************)
