open Lib
open Formulas
open Prop
open Dp
open Fol
open Skolem
open Herbrand
open Meson
open Equal

(* Warnings the book's style trips in this file; the rest of the
   library compiles with them on.  See lib/dune. *)
[@@@warning "-8-10-39"]

(* ========================================================================= *)
(* Special procedures for decidable subsets of first order logic.            *)
(*                                                                           *)
(* Copyright (c) 2003-2007, John Harrison. (See "LICENSE.txt" for details.)  *)
(* ========================================================================= *)

(***
meson {%fol|forall x. p(x)|};;
tab {%fol|forall x. p(x)|};;
 ***)

(* ------------------------------------------------------------------------- *)
(* Resolution does actually terminate with failure in simple cases!          *)
(* ------------------------------------------------------------------------- *)

(***
resolution {%fol|forall x. p(x)|};;
 ***)

(* ------------------------------------------------------------------------- *)
(* The Los example; see how Skolemized form has no non-nullary functions.    *)
(* ------------------------------------------------------------------------- *)


(* Kept at top level: the examples below reuse it, as the toplevel did. *)
let los =
 {%fol|(forall x y z. P(x,y) /\ P(y,z) ==> P(x,z)) /\
   (forall x y z. Q(x,y) /\ Q(y,z) ==> Q(x,z)) /\
   (forall x y. P(x,y) ==> P(y,x)) /\
   (forall x y. P(x,y) \/ Q(x,y))
   ==> (forall x y. P(x,y)) \/ (forall x y. Q(x,y))|};;

let%expect_test "eg: The Los example; see how Skolemized form has no non-nullary functions" =
  print_fol_formula
    (los);
  print_fol_formula
    (skolemize(Not los));
  (* ------------------------------------------------------------------------- *)
  (* The old DP procedure works.                                               *)
  (* ------------------------------------------------------------------------- *)
  print_int
    (davisputnam los);
  [%expect {|
    <<(forall x y z. P(x,y) /\ P(y,z) ==> P(x,z)) /\
      (forall x y z. Q(x,y) /\ Q(y,z) ==> Q(x,z)) /\
      (forall x y. P(x,y) ==> P(y,x)) /\ (forall x y. P(x,y) \/ Q(x,y)) ==>
      (forall x y. P(x,y)) \/ (forall x y. Q(x,y))>><<(((~P(x,y) \/ ~P(y,z)) \/
                                                        P(x,z)) /\
                                                       ((~Q(x,y) \/ ~Q(y,z)) \/
                                                        Q(x,z)) /\
                                                       (~P(x,y) \/ P(y,x)) /\
                                                       (P(x,y) \/ Q(x,y))) /\
                                                      ~P(c_x,c_y) /\
                                                      ~Q(c_x',c_y')>>0 ground instances tried; 0 items in list
    0 ground instances tried; 0 items in list
    1 ground instances tried; 5 items in list
    2 ground instances tried; 7 items in list
    3 ground instances tried; 9 items in list
    4 ground instances tried; 11 items in list
    5 ground instances tried; 15 items in list
    6 ground instances tried; 17 items in list
    7 ground instances tried; 19 items in list
    8 ground instances tried; 21 items in list
    9 ground instances tried; 25 items in list
    10 ground instances tried; 27 items in list
    11 ground instances tried; 29 items in list
    12 ground instances tried; 31 items in list
    13 ground instances tried; 35 items in list
    14 ground instances tried; 37 items in list
    15 ground instances tried; 39 items in list
    16 ground instances tried; 41 items in list
    17 ground instances tried; 45 items in list
    18 ground instances tried; 47 items in list
    19 ground instances tried; 49 items in list
    20 ground instances tried; 51 items in list
    21 ground instances tried; 55 items in list
    22 ground instances tried; 56 items in list
    23 ground instances tried; 58 items in list
    24 ground instances tried; 60 items in list
    25 ground instances tried; 64 items in list
    26 ground instances tried; 66 items in list
    27 ground instances tried; 68 items in list
    28 ground instances tried; 70 items in list
    29 ground instances tried; 74 items in list
    30 ground instances tried; 76 items in list
    31 ground instances tried; 78 items in list
    32 ground instances tried; 80 items in list
    33 ground instances tried; 84 items in list
    34 ground instances tried; 86 items in list
    35 ground instances tried; 88 items in list
    36 ground instances tried; 90 items in list
    37 ground instances tried; 94 items in list
    38 ground instances tried; 96 items in list
    39 ground instances tried; 98 items in list
    40 ground instances tried; 100 items in list
    41 ground instances tried; 104 items in list
    42 ground instances tried; 106 items in list
    43 ground instances tried; 107 items in list
    44 ground instances tried; 109 items in list
    45
    |}]
;;

(* ------------------------------------------------------------------------- *)
(* However, we can just form all the ground instances.                       *)
(* ------------------------------------------------------------------------- *)

let aedecide fm =
  let sfm = skolemize(Not fm) in
  let fvs = fv sfm
  and cnsts,funcs = partition (fun (_,ar) -> ar = 0) (functions sfm) in
  if funcs <> [] then failwith "Not decidable" else
  let consts = if cnsts = [] then ["c",0] else cnsts in
  let cntms = map (fun (c,_) -> Fn(c,[])) consts in
  let alltuples = groundtuples cntms [] 0 (length fvs) in
  let cjs = simpcnf sfm in
  let grounds = map
   (fun tup -> image (image (subst (fpf fvs tup))) cjs) alltuples in
  not(dpll(unions grounds));;

(* ------------------------------------------------------------------------- *)
(* In this case it's quicker.                                                *)
(* ------------------------------------------------------------------------- *)

let%expect_test "eg: In this case it's quicker" =
  print_bool
    (aedecide los);
  [%expect {| true |}]
;;


(* ------------------------------------------------------------------------- *)
(* Show how we need to do PNF transformation with care.                      *)
(* ------------------------------------------------------------------------- *)

let%expect_test "eg: Show how we need to do PNF transformation with care" =
  let fm = {%fol|(forall x. p(x)) \/ (exists y. p(y))|} in
  print_fol_formula
    (fm);
  print_fol_formula
    (pnf fm);
  (* ------------------------------------------------------------------------- *)
  (* Also the group theory problem.                                            *)
  (* ------------------------------------------------------------------------- *)
  print_bool
    (aedecide
     {%fol|(forall x. P(1,x,x)) /\ (forall x. P(x,x,1)) /\
       (forall u v w x y z.
            P(x,y,u) /\ P(y,z,w) ==> (P(x,w,v) <=> P(u,z,v)))
       ==> forall a b c. P(a,b,c) ==> P(b,a,c)|});
  print_bool
    (aedecide
     {%fol|(forall x. P(x,x,1)) /\
       (forall u v w x y z.
            P(x,y,u) /\ P(y,z,w) ==> (P(x,w,v) <=> P(u,z,v)))
       ==> forall a b c. P(a,b,c) ==> P(b,a,c)|});
  (* ------------------------------------------------------------------------- *)
  (* A bigger example.                                                         *)
  (* ------------------------------------------------------------------------- *)
  print_bool
    (aedecide
     {%fol|(exists x. P(x)) /\ (exists x. G(x))
       ==> ((forall x. P(x) ==> H(x)) /\ (forall x. G(x) ==> J(x)) <=>
            (forall x y. P(x) /\ G(y) ==> H(x) /\ J(y)))|});
  [%expect {| <<(forall x. p(x)) \/ (exists y. p(y))>><<forall x. exists y. p(x) \/ p(y)>>truefalsetrue |}]
;;


(* ------------------------------------------------------------------------- *)
(* The following, however, doesn't work with aedecide.                       *)
(* ------------------------------------------------------------------------- *)

(*** This is p18

aedecide {%fol|exists y. forall x. P(y) ==> P(x)|};;

davisputnam {%fol|exists y. forall x. P(y) ==> P(x)|};;

 ***)

(* ------------------------------------------------------------------------- *)
(* Simple-minded miniscoping procedure.                                      *)
(* ------------------------------------------------------------------------- *)

let separate x cjs =
  let yes,no = partition (mem x ** fv) cjs in
  if yes = [] then list_conj no
  else if no = [] then Exists(x,list_conj yes)
  else And(Exists(x,list_conj yes),list_conj no);;

let rec pushquant x p =
  if not (mem x (fv p)) then p else
  let djs = purednf(nnf p) in
  list_disj (map (separate x) djs);;

let rec miniscope fm =
  match fm with
    Not p -> Not(miniscope p)
  | And(p,q) -> And(miniscope p,miniscope q)
  | Or(p,q) -> Or(miniscope p,miniscope q)
  | Forall(x,p) -> Not(pushquant x (Not(miniscope p)))
  | Exists(x,p) -> pushquant x (miniscope p)
  | _ -> fm;;

let%expect_test "eg: Examples" =
  print_fol_formula
    (miniscope(nnf {%fol|exists y. forall x. P(y) ==> P(x)|}));
  let fm = miniscope(nnf
   {%fol|(forall x y. exists z. forall w. P(x) /\ Q(y) ==> R(z) /\ U(w))
     ==> (exists x y. P(x) /\ Q(y)) ==> (exists z. R(z))|}) in
  print_fol_formula
    (fm);
  print_fol_formula
    (pnf(nnf fm));
  [%expect {|
    <<(exists y. ~P(y)) \/ (forall x. P(x))>><<((exists x. P(x)) /\
                                                (forall z. ~R(z)) /\
                                                (exists w. ~U(w)) /\
                                                (exists y. Q(y)) \/
                                                (exists x. P(x)) /\
                                                (forall z. ~R(z)) /\
                                                (exists y. Q(y)) \/
                                                (exists x. P(x)) /\
                                                (exists w. ~U(w)) /\
                                                (exists y. Q(y))) \/
                                               ~((exists x. P(x)) /\
                                                 (exists y. Q(y))) \/
                                               (exists z. R(z))>><<forall z z' x y.
                                                                     exists x' w y'.
                                                                       (P(
                                                                        x') /\
                                                                        ~R(z) /\
                                                                        ~U(w) /\
                                                                        Q(
                                                                        y') \/
                                                                        P(
                                                                        x') /\
                                                                        ~R(z') /\
                                                                        Q(
                                                                        w) \/
                                                                        P(
                                                                        x') /\
                                                                        ~U(w) /\
                                                                        Q(
                                                                        y')) \/
                                                                       (~P(x) \/
                                                                        ~Q(y)) \/
                                                                       R(
                                                                       x')>>
    |}]
;;


(* ------------------------------------------------------------------------- *)
(* Stronger version of "aedecide" similar to Wang's classic procedure.       *)
(* ------------------------------------------------------------------------- *)

let wang fm = aedecide(miniscope(nnf(simplify fm)));;

(* ------------------------------------------------------------------------- *)
(* It works well on simple monadic formulas.                                 *)
(* ------------------------------------------------------------------------- *)

let%expect_test "eg: It works well on simple monadic formulas" =
  print_bool
    (wang
     {%fol|(forall x y. exists z. forall w. P(x) /\ Q(y) ==> R(z) /\ U(w))
       ==> (exists x y. P(x) /\ Q(y)) ==> (exists z. R(z))|});
  (* ------------------------------------------------------------------------- *)
  (* But not on this one!                                                      *)
  (* ------------------------------------------------------------------------- *)
  print_fol_formula
    (pnf(nnf(miniscope(nnf
     {%fol|((exists x. forall y. P(x) <=> P(y)) <=>
        ((exists x. Q(x)) <=> (forall y. Q(y)))) <=>
       ((exists x. forall y. Q(x) <=> Q(y)) <=>
        ((exists x. P(x)) <=> (forall y. P(y))))|}))));
  [%expect {|
    true<<forall y y' y'' y''' y'''' y''''' y'''''' x y''''''' y'''''''' y''''''''' y'''''''''' y''''''''''' y'''''''''''' y''''''''''''' x' x''.
            exists x''' x'''' y'''''''''''''' x''''' y''''''''''''''' x'''''' x''''''' y'''''''''''''''' x'''''''' y'''''''''''''''''.
              (((P(x''') /\ ~P(x''')) /\ P(y) /\ (~P(y) \/ P(y)) \/
                (P(x''') /\ ~P(x''')) /\ ~P(y') /\ (~P(y') \/ P(y')) \/
                (P(x''') /\ ~P(x''')) /\ (~P(y'') \/ P(y'')) \/
                P(x''') /\ P(y''') /\ ~P(y''') /\ (~P(y''') \/ P(y''')) \/
                P(x''') /\ P(y'''') /\ (~P(y'''') \/ P(y'''')) \/
                ~P(x''') /\ P(y''''') /\ ~P(y''''') /\ (~P(y''''') \/ P(y''''')) \/
                ~P(x''') /\ ~P(y'''''') /\ (~P(y'''''') \/ P(y''''''))) /\
               (Q(x'''') /\ Q(y) \/ ~Q(y') /\ ~Q(x'''')) \/
               ((~P(x) \/ P(x)) /\
                (~P(x) \/ ~P(x''')) /\
                (P(x) \/ P(x'''')) /\ (~P(y'''''''''''''') \/ P(y''''''''''''''))) /\
               (Q(x''''') /\ ~Q(y''''''''''''''') \/ ~Q(x) /\ Q(x))) /\
              (((Q(x'''''') /\ ~Q(x'''''')) /\ Q(y) /\ (~Q(y) \/ Q(y)) \/
                (Q(x'''''') /\ ~Q(x'''''')) /\ ~Q(y') /\ (~Q(y') \/ Q(y')) \/
                (Q(x'''''') /\ ~Q(x'''''')) /\ (~Q(y'') \/ Q(y'')) \/
                Q(x'''''') /\ Q(y''') /\ ~Q(y''') /\ (~Q(y''') \/ Q(y''')) \/
                Q(x'''''') /\ Q(y'''') /\ (~Q(y'''') \/ Q(y'''')) \/
                ~Q(x'''''') /\
                Q(y''''') /\ ~Q(y''''') /\ (~Q(y''''') \/ Q(y''''')) \/
                ~Q(x'''''') /\ ~Q(y'''''') /\ (~Q(y'''''') \/ Q(y''''''))) /\
               (P(x''''''') /\ P(y) \/ ~P(y') /\ ~P(x''''''')) \/
               ((~Q(x) \/ Q(x)) /\
                (~Q(x) \/ ~Q(x'''''')) /\
                (Q(x) \/ Q(x''''''')) /\
                (~Q(y'''''''''''''''') \/ Q(y''''''''''''''''))) /\
               (P(x'''''''') /\ ~P(y''''''''''''''''') \/ ~P(x) /\ P(x))) \/
              (((P(x''') /\ ~P(x''')) /\
                P(y''''''') /\ (~P(y''''''') \/ P(y''''''')) \/
                (P(x''') /\ ~P(x''')) /\
                ~P(y'''''''') /\ (~P(y'''''''') \/ P(y'''''''')) \/
                (P(x''') /\ ~P(x''')) /\ (~P(y''''''''') \/ P(y''''''''')) \/
                P(x''') /\
                P(y'''''''''') /\
                ~P(y'''''''''') /\ (~P(y'''''''''') \/ P(y'''''''''')) \/
                P(x''') /\
                P(y''''''''''') /\ (~P(y''''''''''') \/ P(y''''''''''')) \/
                ~P(x''') /\
                P(y'''''''''''') /\
                ~P(y'''''''''''') /\ (~P(y'''''''''''') \/ P(y'''''''''''')) \/
                ~P(x''') /\
                ~P(y''''''''''''') /\ (~P(y''''''''''''') \/ P(y'''''''''''''))) /\
               (Q(x'''') /\ ~Q(y'''''''''''''') \/ ~Q(y''''''') /\ Q(y''''''')) \/
               ((~P(x') \/ P(x')) /\
                (~P(x') \/ ~P(x''')) /\
                (P(x') \/ P(x'''')) /\
                (~P(y'''''''''''''') \/ P(y''''''''''''''))) /\
               (Q(x''''') /\ Q(x') \/ ~Q(x'') /\ ~Q(x'''''))) /\
              (((Q(y''''''''''''''') /\ ~Q(y''''''''''''''')) /\
                Q(y''''''') /\ (~Q(y''''''') \/ Q(y''''''')) \/
                (Q(y''''''''''''''') /\ ~Q(y''''''''''''''')) /\
                ~Q(y'''''''') /\ (~Q(y'''''''') \/ Q(y'''''''')) \/
                (Q(y''''''''''''''') /\ ~Q(y''''''''''''''')) /\
                (~Q(y''''''''') \/ Q(y''''''''')) \/
                Q(y''''''''''''''') /\
                Q(y'''''''''') /\
                ~Q(y'''''''''') /\ (~Q(y'''''''''') \/ Q(y'''''''''')) \/
                Q(y''''''''''''''') /\
                Q(y''''''''''') /\ (~Q(y''''''''''') \/ Q(y''''''''''')) \/
                ~Q(y''''''''''''''') /\
                Q(y'''''''''''') /\
                ~Q(y'''''''''''') /\ (~Q(y'''''''''''') \/ Q(y'''''''''''')) \/
                ~Q(y''''''''''''''') /\
                ~Q(y''''''''''''') /\ (~Q(y''''''''''''') \/ Q(y'''''''''''''))) /\
               (P(x'''''') /\ ~P(x''''''') \/ ~P(y''''''') /\ P(y''''''')) \/
               ((~Q(x') \/ Q(x')) /\
                (~Q(x') \/ ~Q(y''''''''''''''')) /\
                (Q(x') \/ Q(x'''''')) /\ (~Q(x''''''') \/ Q(x'''''''))) /\
               (P(y'''''''''''''''') /\ P(x') \/ ~P(x'') /\ ~P(y'''''''''''''''')))>>
    |}]
;;


(* ------------------------------------------------------------------------- *)
(* Checking classic Aristotelean syllogisms.                                 *)
(* ------------------------------------------------------------------------- *)

let atom p x = Atom(R(p,[Var x]));;

let premiss_A (p,q) = Forall("x",Imp(atom p "x",atom q "x"))
and premiss_E (p,q) = Forall("x",Imp(atom p "x",Not(atom q "x")))
and premiss_I (p,q) = Exists("x",And(atom p "x",atom q "x"))
and premiss_O (p,q) = Exists("x",And(atom p "x",Not(atom q "x")));;

let anglicize_premiss fm =
  match fm with
    Forall(_,Imp(Atom(R(p,_)),Atom(R(q,_)))) ->  "all "^p^" are "^q
  | Forall(_,Imp(Atom(R(p,_)),Not(Atom(R(q,_))))) ->  "no "^p^" are "^q
  | Exists(_,And(Atom(R(p,_)),Atom(R(q,_)))) ->  "some "^p^" are "^q
  | Exists(_,And(Atom(R(p,_)),Not(Atom(R(q,_))))) ->
        "some "^p^" are not "^q;;

let anglicize_syllogism (Imp(And(t1,t2),t3)) =
  "If " ^ anglicize_premiss t1 ^ " and " ^ anglicize_premiss t2 ^
  ", then " ^ anglicize_premiss t3;;

let all_possible_syllogisms =
  let sylltypes = [premiss_A; premiss_E; premiss_I; premiss_O] in
  let prems1 = allpairs (fun x -> x) sylltypes ["M","P"; "P","M"]
  and prems2 = allpairs (fun x -> x) sylltypes ["S","M"; "M","S"]
  and prems3 = allpairs (fun x -> x) sylltypes ["S","P"] in
  allpairs mk_imp (allpairs mk_and prems1 prems2) prems3;;

let%expect_test _ =
  let all_valid_syllogisms = filter aedecide all_possible_syllogisms in
  print_list print_fol_formula
    (all_valid_syllogisms);
  print_int
    (length all_valid_syllogisms);
  print_list print_quoted
    (map anglicize_syllogism all_valid_syllogisms);
  [%expect {|
    [<<(forall x. M(x) ==> P(x)) /\ (forall x. S(x) ==> M(x)) ==>
       (forall x. S(x) ==> P(x))>>; <<(forall x. M(x) ==> P(x)) /\
                                      (exists x. S(x) /\ M(x)) ==>
                                      (exists x. S(x) /\ P(x))>>; <<(forall x.
                                                                       M(
                                                                       x) ==>
                                                                       P(
                                                                       x)) /\
                                                                    (exists x.
                                                                       M(
                                                                       x) /\ S(
                                                                       x)) ==>
                                                                    (exists x.
                                                                       S(
                                                                       x) /\ P(
                                                                       x))>>;
    <<(forall x. P(x) ==> M(x)) /\ (forall x. S(x) ==> ~M(x)) ==>
      (forall x. S(x) ==> ~P(x))>>; <<(forall x. P(x) ==> M(x)) /\
                                      (forall x. M(x) ==> ~S(x)) ==>
                                      (forall x. S(x) ==> ~P(x))>>; <<(forall x.
                                                                        P(
                                                                        x) ==>
                                                                        M(
                                                                        x)) /\
                                                                      (exists x.
                                                                        S(
                                                                        x) /\
                                                                        ~M(x)) ==>
                                                                      (exists x.
                                                                        S(
                                                                        x) /\
                                                                        ~P(x))>>;
    <<(forall x. M(x) ==> ~P(x)) /\ (forall x. S(x) ==> M(x)) ==>
      (forall x. S(x) ==> ~P(x))>>; <<(forall x. M(x) ==> ~P(x)) /\
                                      (exists x. S(x) /\ M(x)) ==>
                                      (exists x. S(x) /\ ~P(x))>>; <<(forall x.
                                                                        M(
                                                                        x) ==>
                                                                        ~P(x)) /\
                                                                     (exists x.
                                                                        M(
                                                                        x) /\
                                                                        S(
                                                                        x)) ==>
                                                                     (exists x.
                                                                        S(
                                                                        x) /\
                                                                        ~P(x))>>;
    <<(forall x. P(x) ==> ~M(x)) /\ (forall x. S(x) ==> M(x)) ==>
      (forall x. S(x) ==> ~P(x))>>; <<(forall x. P(x) ==> ~M(x)) /\
                                      (exists x. S(x) /\ M(x)) ==>
                                      (exists x. S(x) /\ ~P(x))>>; <<(forall x.
                                                                        P(
                                                                        x) ==>
                                                                        ~M(x)) /\
                                                                     (exists x.
                                                                        M(
                                                                        x) /\
                                                                        S(
                                                                        x)) ==>
                                                                     (exists x.
                                                                        S(
                                                                        x) /\
                                                                        ~P(x))>>;
    <<(exists x. M(x) /\ P(x)) /\ (forall x. M(x) ==> S(x)) ==>
      (exists x. S(x) /\ P(x))>>; <<(exists x. P(x) /\ M(x)) /\
                                    (forall x. M(x) ==> S(x)) ==>
                                    (exists x. S(x) /\ P(x))>>; <<(exists x.
                                                                     M(x) /\
                                                                     ~P(x)) /\
                                                                  (forall x.
                                                                     M(x) ==>
                                                                     S(x)) ==>
                                                                  (exists x.
                                                                     S(x) /\
                                                                     ~P(x))>>]15["If all M are P and all S are M, then all S are P"; "If all M are P and some S are M, then some S are P"; "If all M are P and some M are S, then some S are P"; "If all P are M and no S are M, then no S are P"; "If all P are M and no M are S, then no S are P"; "If all P are M and some S are not M, then some S are not P"; "If no M are P and all S are M, then no S are P"; "If no M are P and some S are M, then some S are not P"; "If no M are P and some M are S, then some S are not P"; "If no P are M and all S are M, then no S are P"; "If no P are M and some S are M, then some S are not P"; "If no P are M and some M are S, then some S are not P"; "If some M are P and all M are S, then some S are P"; "If some P are M and all M are S, then some S are P"; "If some M are not P and all M are S, then some S are not P"]
    |}]
;;


(* ------------------------------------------------------------------------- *)
(* We can "fix" the traditional list by assuming nonemptiness.               *)
(* ------------------------------------------------------------------------- *)

let all_possible_syllogisms' =
  let p =
    {%fol|(exists x. P(x)) /\ (exists x. M(x)) /\ (exists x. S(x))|} in
  map (fun t -> Imp(p,t)) all_possible_syllogisms;;


let%expect_test _ =
  let all_valid_syllogisms' = filter aedecide all_possible_syllogisms' in
  print_list print_fol_formula
    (all_valid_syllogisms');
  print_int
    (length all_valid_syllogisms');
  print_list print_quoted
    (map (anglicize_syllogism ** consequent) all_valid_syllogisms');
  [%expect {|
    [<<(exists x. P(x)) /\ (exists x. M(x)) /\ (exists x. S(x)) ==>
       (forall x. M(x) ==> P(x)) /\ (forall x. S(x) ==> M(x)) ==>
       (forall x. S(x) ==> P(x))>>; <<(exists x. P(x)) /\
                                      (exists x. M(x)) /\ (exists x. S(x)) ==>
                                      (forall x. M(x) ==> P(x)) /\
                                      (forall x. S(x) ==> M(x)) ==>
                                      (exists x. S(x) /\ P(x))>>; <<(exists x.
                                                                       P(x)) /\
                                                                    (exists x.
                                                                       M(x)) /\
                                                                    (exists x.
                                                                       S(x)) ==>
                                                                    (forall x.
                                                                       M(
                                                                       x) ==>
                                                                       P(
                                                                       x)) /\
                                                                    (forall x.
                                                                       M(
                                                                       x) ==>
                                                                       S(
                                                                       x)) ==>
                                                                    (exists x.
                                                                       S(
                                                                       x) /\ P(
                                                                       x))>>;
    <<(exists x. P(x)) /\ (exists x. M(x)) /\ (exists x. S(x)) ==>
      (forall x. M(x) ==> P(x)) /\ (exists x. S(x) /\ M(x)) ==>
      (exists x. S(x) /\ P(x))>>; <<(exists x. P(x)) /\
                                    (exists x. M(x)) /\ (exists x. S(x)) ==>
                                    (forall x. M(x) ==> P(x)) /\
                                    (exists x. M(x) /\ S(x)) ==>
                                    (exists x. S(x) /\ P(x))>>; <<(exists x. P(x)) /\
                                                                  (exists x. M(x)) /\
                                                                  (exists x. S(x)) ==>
                                                                  (forall x.
                                                                     P(x) ==>
                                                                     M(x)) /\
                                                                  (forall x.
                                                                     M(x) ==>
                                                                     S(x)) ==>
                                                                  (exists x.
                                                                     S(x) /\ P(x))>>;
    <<(exists x. P(x)) /\ (exists x. M(x)) /\ (exists x. S(x)) ==>
      (forall x. P(x) ==> M(x)) /\ (forall x. S(x) ==> ~M(x)) ==>
      (forall x. S(x) ==> ~P(x))>>; <<(exists x. P(x)) /\
                                      (exists x. M(x)) /\ (exists x. S(x)) ==>
                                      (forall x. P(x) ==> M(x)) /\
                                      (forall x. S(x) ==> ~M(x)) ==>
                                      (exists x. S(x) /\ ~P(x))>>; <<(exists x.
                                                                        P(x)) /\
                                                                     (exists x.
                                                                        M(x)) /\
                                                                     (exists x.
                                                                        S(x)) ==>
                                                                     (forall x.
                                                                        P(
                                                                        x) ==>
                                                                        M(
                                                                        x)) /\
                                                                     (forall x.
                                                                        M(
                                                                        x) ==>
                                                                        ~S(x)) ==>
                                                                     (forall x.
                                                                        S(
                                                                        x) ==>
                                                                        ~P(x))>>;
    <<(exists x. P(x)) /\ (exists x. M(x)) /\ (exists x. S(x)) ==>
      (forall x. P(x) ==> M(x)) /\ (forall x. M(x) ==> ~S(x)) ==>
      (exists x. S(x) /\ ~P(x))>>; <<(exists x. P(x)) /\
                                     (exists x. M(x)) /\ (exists x. S(x)) ==>
                                     (forall x. P(x) ==> M(x)) /\
                                     (exists x. S(x) /\ ~M(x)) ==>
                                     (exists x. S(x) /\ ~P(x))>>; <<(exists x.
                                                                       P(x)) /\
                                                                    (exists x.
                                                                       M(x)) /\
                                                                    (exists x.
                                                                       S(x)) ==>
                                                                    (forall x.
                                                                       M(
                                                                       x) ==>
                                                                       ~P(x)) /\
                                                                    (forall x.
                                                                       S(
                                                                       x) ==>
                                                                       M(
                                                                       x)) ==>
                                                                    (forall x.
                                                                       S(
                                                                       x) ==>
                                                                       ~P(x))>>;
    <<(exists x. P(x)) /\ (exists x. M(x)) /\ (exists x. S(x)) ==>
      (forall x. M(x) ==> ~P(x)) /\ (forall x. S(x) ==> M(x)) ==>
      (exists x. S(x) /\ ~P(x))>>; <<(exists x. P(x)) /\
                                     (exists x. M(x)) /\ (exists x. S(x)) ==>
                                     (forall x. M(x) ==> ~P(x)) /\
                                     (forall x. M(x) ==> S(x)) ==>
                                     (exists x. S(x) /\ ~P(x))>>; <<(exists x.
                                                                       P(x)) /\
                                                                    (exists x.
                                                                       M(x)) /\
                                                                    (exists x.
                                                                       S(x)) ==>
                                                                    (forall x.
                                                                       M(
                                                                       x) ==>
                                                                       ~P(x)) /\
                                                                    (exists x.
                                                                       S(
                                                                       x) /\ M(
                                                                       x)) ==>
                                                                    (exists x.
                                                                       S(
                                                                       x) /\
                                                                       ~P(x))>>;
    <<(exists x. P(x)) /\ (exists x. M(x)) /\ (exists x. S(x)) ==>
      (forall x. M(x) ==> ~P(x)) /\ (exists x. M(x) /\ S(x)) ==>
      (exists x. S(x) /\ ~P(x))>>; <<(exists x. P(x)) /\
                                     (exists x. M(x)) /\ (exists x. S(x)) ==>
                                     (forall x. P(x) ==> ~M(x)) /\
                                     (forall x. S(x) ==> M(x)) ==>
                                     (forall x. S(x) ==> ~P(x))>>; <<(exists x.
                                                                        P(x)) /\
                                                                     (exists x.
                                                                        M(x)) /\
                                                                     (exists x.
                                                                        S(x)) ==>
                                                                     (forall x.
                                                                        P(
                                                                        x) ==>
                                                                        ~M(x)) /\
                                                                     (forall x.
                                                                        S(
                                                                        x) ==>
                                                                        M(
                                                                        x)) ==>
                                                                     (exists x.
                                                                        S(
                                                                        x) /\
                                                                        ~P(x))>>;
    <<(exists x. P(x)) /\ (exists x. M(x)) /\ (exists x. S(x)) ==>
      (forall x. P(x) ==> ~M(x)) /\ (forall x. M(x) ==> S(x)) ==>
      (exists x. S(x) /\ ~P(x))>>; <<(exists x. P(x)) /\
                                     (exists x. M(x)) /\ (exists x. S(x)) ==>
                                     (forall x. P(x) ==> ~M(x)) /\
                                     (exists x. S(x) /\ M(x)) ==>
                                     (exists x. S(x) /\ ~P(x))>>; <<(exists x.
                                                                       P(x)) /\
                                                                    (exists x.
                                                                       M(x)) /\
                                                                    (exists x.
                                                                       S(x)) ==>
                                                                    (forall x.
                                                                       P(
                                                                       x) ==>
                                                                       ~M(x)) /\
                                                                    (exists x.
                                                                       M(
                                                                       x) /\ S(
                                                                       x)) ==>
                                                                    (exists x.
                                                                       S(
                                                                       x) /\
                                                                       ~P(x))>>;
    <<(exists x. P(x)) /\ (exists x. M(x)) /\ (exists x. S(x)) ==>
      (exists x. M(x) /\ P(x)) /\ (forall x. M(x) ==> S(x)) ==>
      (exists x. S(x) /\ P(x))>>; <<(exists x. P(x)) /\
                                    (exists x. M(x)) /\ (exists x. S(x)) ==>
                                    (exists x. P(x) /\ M(x)) /\
                                    (forall x. M(x) ==> S(x)) ==>
                                    (exists x. S(x) /\ P(x))>>; <<(exists x. P(x)) /\
                                                                  (exists x. M(x)) /\
                                                                  (exists x. S(x)) ==>
                                                                  (exists x.
                                                                     M(x) /\
                                                                     ~P(x)) /\
                                                                  (forall x.
                                                                     M(x) ==>
                                                                     S(x)) ==>
                                                                  (exists x.
                                                                     S(x) /\
                                                                     ~P(x))>>]24["If all M are P and all S are M, then all S are P"; "If all M are P and all S are M, then some S are P"; "If all M are P and all M are S, then some S are P"; "If all M are P and some S are M, then some S are P"; "If all M are P and some M are S, then some S are P"; "If all P are M and all M are S, then some S are P"; "If all P are M and no S are M, then no S are P"; "If all P are M and no S are M, then some S are not P"; "If all P are M and no M are S, then no S are P"; "If all P are M and no M are S, then some S are not P"; "If all P are M and some S are not M, then some S are not P"; "If no M are P and all S are M, then no S are P"; "If no M are P and all S are M, then some S are not P"; "If no M are P and all M are S, then some S are not P"; "If no M are P and some S are M, then some S are not P"; "If no M are P and some M are S, then some S are not P"; "If no P are M and all S are M, then no S are P"; "If no P are M and all S are M, then some S are not P"; "If no P are M and all M are S, then some S are not P"; "If no P are M and some S are M, then some S are not P"; "If no P are M and some M are S, then some S are not P"; "If some M are P and all M are S, then some S are P"; "If some P are M and all M are S, then some S are P"; "If some M are not P and all M are S, then some S are not P"]
    |}]
;;

(* ------------------------------------------------------------------------- *)
(* Decide a formula on all models of size n.                                 *)
(* ------------------------------------------------------------------------- *)

let rec alltuples n l =
  if n = 0 then [[]] else
  let tups = alltuples (n - 1) l in
  allpairs (fun h t -> h::t) l tups;;

let allmappings dom ran =
  itlist (fun p -> allpairs (valmod p) ran) dom [undef];;

let alldepmappings dom ran =
  itlist (fun (p,n) -> allpairs (valmod p) (ran n)) dom [undef];;

let allfunctions dom n = allmappings (alltuples n dom) dom;;

let allpredicates dom n = allmappings (alltuples n dom) [false;true];;

let decide_finite n fm =
  let funcs = functions fm and preds = predicates fm and dom = 1--n in
  let fints = alldepmappings funcs (allfunctions dom)
  and pints = alldepmappings preds (allpredicates dom) in
  let interps = allpairs (fun f p -> dom,f,p) fints pints in
  let fm' = generalize fm in
  forall (fun md -> holds md undefined fm') interps;;

(* ------------------------------------------------------------------------- *)
(* Decision procedure in principle for formulas with finite model property.  *)
(* ------------------------------------------------------------------------- *)

let limmeson n fm =
  let cls = simpcnf(specialize(pnf fm)) in
  let rules = itlist ((@) ** contrapositives) cls [] in
  mexpand rules [] False (fun x -> x) (undefined,n,0);;

let limited_meson n fm =
  let fm1 = askolemize(Not(generalize fm)) in
  map (limmeson n ** list_conj) (simpdnf fm1);;

let decide_fmp fm =
  let rec test n =
    try limited_meson n fm; true with Failure _ ->
    if decide_finite n fm then test (n + 1) else false in
  test 1;;

let%expect_test _ =
  print_bool
    (decide_fmp
     {%fol|(forall x y. R(x,y) \/ R(y,x)) ==> forall x. R(x,x)|});
  print_bool
    (decide_fmp
     {%fol|(forall x y z. R(x,y) /\ R(y,z) ==> R(x,z)) ==> forall x. R(x,x)|});
  (*** This fails to terminate: has countermodels, but only infinite ones
  decide_fmp
   {%fol|~((forall x. ~R(x,x)) /\
       (forall x. exists z. R(x,z)) /\
       (forall x y z. R(x,y) /\ R(y,z) ==> R(x,z)))|};;
  ****)
  [%expect {| truefalse |}]
;;


(* ------------------------------------------------------------------------- *)
(* Semantic decision procedure for the monadic fragment.                     *)
(* ------------------------------------------------------------------------- *)

let decide_monadic fm =
  let funcs = functions fm and preds = predicates fm in
  let monadic,other = partition (fun (_,ar) -> ar = 1) preds in
  if funcs <> [] || exists (fun (_,ar) -> ar > 1) other
  then failwith "Not in the monadic subset" else
  let n = funpow (length monadic) (( * ) 2) 1 in
  decide_finite n fm;;

let%expect_test "eg" =
  print_bool
    (decide_monadic
     {%fol|((exists x. forall y. P(x) <=> P(y)) <=>
        ((exists x. Q(x)) <=> (forall y. Q(y)))) <=>
        ((exists x. forall y. Q(x) <=> Q(y)) <=>
       ((exists x. P(x)) <=> (forall y. P(y))))|});
  (**** This is not feasible
  decide_monadic
   {%fol|(forall x y. exists z. forall w. P(x) /\ Q(y) ==> R(z) /\ U(w))
     ==> (exists x y. P(x) /\ Q(y)) ==> (exists z. R(z))|};;
   ****)
  [%expect {| true |}]
;;


(* ------------------------------------------------------------------------- *)
(* Little auxiliary results for failure of finite model property.            *)
(* ------------------------------------------------------------------------- *)

let%expect_test "eg: Little auxiliary results for failure of finite model property" =
  (*** Our claimed equivalences are indeed correct ***)
  print_list print_int
    (meson
     {%fol|(exists x y z. forall u.
            R(x,x) \/ ~R(x,u) \/ (R(x,y) /\ R(y,z) /\ ~R(x,z))) <=>
       ~((forall x. ~R(x,x)) /\
         (forall x. exists z. R(x,z)) /\
         (forall x y z. R(x,y) /\ R(y,z) ==> R(x,z)))|});
  print_list print_int
    (meson
     {%fol|(exists x. forall y. exists z. R(x,x) \/ ~R(x,y) \/ (R(y,z) /\ ~R(x,z))) <=>
       ~((forall x. ~R(x,x)) /\
         (forall x. exists y. R(x,y) /\ forall z. R(y,z) ==> R(x,z)))|});
  (*** The second formula implies the first ***)
  print_list print_int
    (meson
    {%fol|~((forall x. ~R(x,x)) /\
        (forall x. exists y. R(x,y) /\ forall z. R(y,z) ==> R(x,z)))
      ==> ~((forall x. ~R(x,x)) /\
            (forall x. exists z. R(x,z)) /\
            (forall x y z. R(x,y) /\ R(y,z) ==> R(x,z)))|});
  [%expect {|
    Searching with depth limit 0Searching with depth limit 1
    Searching with depth limit 0Searching with depth limit 1Searching with depth limit 2Searching with depth limit 3
    Searching with depth limit 0Searching with depth limit 1Searching with depth limit 2Searching with depth limit 3Searching with depth limit 4Searching with depth limit 5Searching with depth limit 6Searching with depth limit 7Searching with depth limit 8Searching with depth limit 9
    Searching with depth limit 0Searching with depth limit 1
    [1; 3; 9; 1]Searching with depth limit 0Searching with depth limit 1
    Searching with depth limit 0Searching with depth limit 1Searching with depth limit 2Searching with depth limit 3Searching with depth limit 4Searching with depth limit 5Searching with depth limit 6
    Searching with depth limit 0Searching with depth limit 1Searching with depth limit 2Searching with depth limit 3Searching with depth limit 4
    [1; 6; 4]Searching with depth limit 0Searching with depth limit 1
    Searching with depth limit 0Searching with depth limit 1Searching with depth limit 2Searching with depth limit 3Searching with depth limit 4Searching with depth limit 5
    [1; 5]
    |}]
;;
