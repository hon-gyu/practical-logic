open Lib
open Formulas
open Prop
open Fol
open Skolem
open Tableaux
open Meson
open Equal

(* Warnings the book's style trips in this file; the rest of the
   library compiles with them on.  See lib/dune. *)
[@@@warning "-8-10"]

(* ========================================================================= *)
(* Equality elimination including Brand transformation and relatives.        *)
(*                                                                           *)
(* Copyright (c) 2003-2007, John Harrison. (See "LICENSE.txt" for details.)  *)
(* ========================================================================= *)


let%expect_test _ =
  (* ------------------------------------------------------------------------- *)
  (* The x^2 = 1 implies Abelian problem.                                      *)
  (* ------------------------------------------------------------------------- *)
  print_fol_formula
    (meson
     {%fol|(forall x. P(1,x,x)) /\
       (forall x. P(x,x,1)) /\
       (forall u v w x y z. P(x,y,u) /\ P(y,z,w)
                            ==> (P(x,w,v) <=> P(u,z,v)))
       ==> forall a b c. P(a,b,c) ==> P(b,a,c)|});
  (* ------------------------------------------------------------------------- *)
  (* Lemma for equivalence elimination.                                        *)
  (* ------------------------------------------------------------------------- *)
  print_fol_formula
    (meson
     {%fol|(forall x. R(x,x)) /\
       (forall x y. R(x,y) ==>  R(y,x)) /\
       (forall x y z. R(x,y) /\ R(y,z) ==> R(x,z))
       <=> (forall x y. R(x,y) <=> (forall z. R(x,z) <=> R(y,z)))|});
  [%expect {| |}]
;;

(* ------------------------------------------------------------------------- *)
(* Brand's S and T modifications on clauses.                                 *)
(* ------------------------------------------------------------------------- *)

let rec modify_S cl =
  try let (s,t) = tryfind dest_eq cl in
      let eq1 = mk_eq s t and eq2 = mk_eq t s in
      let sub = modify_S (subtract cl [eq1]) in
      map (insert eq1) sub @ map (insert eq2) sub
  with Failure _ -> [cl];;

let rec modify_T cl =
  match cl with
    (Atom(R("=",[s;t])) as eq)::ps ->
        let ps' = modify_T ps in
        let w = Var(variant "w" (itlist (union ** fv) ps' (fv eq))) in
        Not(mk_eq t w)::(mk_eq s w)::ps'
  | p::ps -> p::(modify_T ps)
  | [] -> [];;

(* ------------------------------------------------------------------------- *)
(* Finding nested non-variable subterms.                                     *)
(* ------------------------------------------------------------------------- *)

let is_nonvar = function (Var x) -> false | _ -> true;;

let find_nestnonvar tm =
  match tm with
    Var x -> failwith "findnvsubt"
  | Fn(f,args) -> find is_nonvar args;;

let rec find_nvsubterm fm =
  match fm with
    Atom(R("=",[s;t])) -> tryfind find_nestnonvar [s;t]
  | Atom(R(p,args)) -> find is_nonvar args
  | Not p -> find_nvsubterm p;;

(* ------------------------------------------------------------------------- *)
(* Replacement (substitution for non-variable) in term and literal.          *)
(* ------------------------------------------------------------------------- *)

let rec replacet rfn tm =
  try apply rfn tm with Failure _ ->
  match tm with
    Fn(f,args) -> Fn(f,map (replacet rfn) args)
  | _ -> tm;;

let replace rfn = onformula (replacet rfn);;

(* ------------------------------------------------------------------------- *)
(* E-modification of a clause.                                               *)
(* ------------------------------------------------------------------------- *)

let rec emodify fvs cls =
  try let t = tryfind find_nvsubterm cls in
      let w = variant "w" fvs in
      let cls' = map (replace (t |=> Var w)) cls in
      emodify (w::fvs) (Not(mk_eq t (Var w))::cls')
  with Failure _ -> cls;;

let modify_E cls = emodify (itlist (union ** fv) cls []) cls;;

(* ------------------------------------------------------------------------- *)
(* Overall Brand transformation.                                             *)
(* ------------------------------------------------------------------------- *)

let brand cls =
  let cls1 = map modify_E cls in
  let cls2 = itlist (union ** modify_S) cls1 [] in
  [mk_eq (Var "x") (Var "x")]::(map modify_T cls2);;

(* ------------------------------------------------------------------------- *)
(* Incorporation into MESON.                                                 *)
(* ------------------------------------------------------------------------- *)

let bpuremeson fm =
  let cls = brand(simpcnf(specialize(pnf fm))) in
  let rules = itlist ((@) ** contrapositives) cls [] in
  deepen (fun n ->
     mexpand rules [] False (fun x -> x) (undefined,n,0); n) 0;;

let bmeson fm =
  let fm1 = askolemize(Not(generalize fm)) in
  map (bpuremeson ** list_conj) (simpdnf fm1);;

let%expect_test "eg: Examples" =
  let emeson fm = meson (equalitize fm) in
  print_fol_formula
    (time bmeson
     {%fol|(exists x. x = f(g(x)) /\ forall x'. x' = f(g(x')) ==> x = x') <=>
       (exists y. y = g(f(y)) /\ forall y'. y' = g(f(y')) ==> y = y')|});
  print_fol_formula
    (time emeson
     {%fol|(exists x. x = f(g(x)) /\ forall x'. x' = f(g(x')) ==> x = x') <=>
       (exists y. y = g(f(y)) /\ forall y'. y' = g(f(y')) ==> y = y')|});
  print_fol_formula
    (time bmeson
     {%fol|(forall x y z. x * (y * z) = (x * y) * z) /\
       (forall x. e * x = x) /\
       (forall x. i(x) * x = e)
       ==> forall x. x * i(x) = e|});
  [%expect {| |}]
;;


(* ------------------------------------------------------------------------- *)
(* Older stuff not now in the text.                                          *)
(* ------------------------------------------------------------------------- *)

let%expect_test "eg: Older stuff not now in the text" =
  let ewd =
   {%fol|(forall x. f(x) ==> g(x)) /\
     (exists x. f(x)) /\
     (forall x y. g(x) /\ g(y) ==> x = y)
     ==> forall y. g(y) ==> f(y)|} in
  print_fol_formula
    (ewd);
  let wishnu =
   {%fol|(exists x. x = f(g(x)) /\ forall x'. x' = f(g(x')) ==> x = x') <=>
     (exists y. y = g(f(y)) /\ forall y'. y' = g(f(y')) ==> y = y')|} in
  print_fol_formula
    (wishnu);
  let group1 =
   {%fol|(forall x y z. x * (y * z) = (x * y) * z) /\
     (forall x. e * x = x) /\
     (forall x. i(x) * x = e)
     ==> forall x. x * e = x|} in
  print_fol_formula
    (group1);
  let group2 =
   {%fol|(forall x y z. x * (y * z) = (x * y) * z) /\
     (forall x. e * x = x) /\
     (forall x. i(x) * x = e)
     ==> forall x. x * i(x) = e|} in
  print_fol_formula
    (group2);
  print_fol_formula
    (time bmeson ewd);
  print_fol_formula
    (time emeson ewd);
  (***********

  time bmeson wishnu;;
  time emeson wishnu;;

  time bmeson group1;;
  time emeson group1;;

  time bmeson group2;;
  time emeson group2;;

   *************)

  (* ------------------------------------------------------------------------- *)
  (* Nice function composition exercise from "Conceptual Mathematics".         *)
  (* ------------------------------------------------------------------------- *)

  (**************

  let fm =
   {%fol|(forall x y z. x * (y * z) = (x * y) * z) /\ p * q * p = p
     ==> exists q'. p * q' * p = p /\ q' * p * q' = q'|};;

  time bmeson fm;;        (** Seems to take a bit longer than below version  **)

  time emeson fm;;        (** Works in 64275 seconds(!), depth 30, on laptop **)

  ****************)

  (**** Some other predicate formulations no longer in the main text

  meson
   {%fol|(forall x. P(1,x,x)) /\
     (forall x. P(i(x),x,1)) /\
     (forall u v w x y z. P(x,y,u) /\ P(y,z,w) ==> (P(x,w,v) <=> P(u,z,v)))
     ==> forall x. P(x,1,x)|};;

  meson
   {%fol|(forall x. P(1,x,x)) /\
     (forall x. P(i(x),x,1)) /\
     (forall u v w x y z. P(x,y,u) /\ P(y,z,w) ==> (P(x,w,v) <=> P(u,z,v)))
     ==> forall x. P(x,i(x),1)|};;

  (* ------------------------------------------------------------------------- *)
  (* See how efficiency drops when we assert completeness.                     *)
  (* ------------------------------------------------------------------------- *)

  meson
   {%fol|(forall x. P(1,x,x)) /\
     (forall x. P(x,x,1)) /\
     (forall x y. exists z. P(x,y,z)) /\
     (forall u v w x y z. P(x,y,u) /\ P(y,z,w) ==> (P(x,w,v) <=> P(u,z,v)))
     ==> forall a b c. P(a,b,c) ==> P(b,a,c)|};;

  ****)

  (*** More reductions, not now explicitly in the text.

  meson
   {%fol|(forall x. R(x,x)) /\
     (forall x y z. R(x,y) /\ R(y,z) ==> R(x,z))
     <=> (forall x y. R(x,y) <=> (forall z. R(y,z) ==> R(x,z)))|};;

  meson
   {%fol|(forall x y. R(x,y) ==>  R(y,x)) <=>
     (forall x y. R(x,y) <=> R(x,y) /\ R(y,x))|};;

  (* ------------------------------------------------------------------------- *)
  (* Show how Equiv' reduces to triviality.                                    *)
  (* ------------------------------------------------------------------------- *)

  meson
   {%fol|(forall x. (forall w. R'(x,w) <=> R'(x,w))) /\
     (forall x y. (forall w. R'(x,w) <=> R'(y,w))
                  ==> (forall w. R'(y,w) <=> R'(x,w))) /\
     (forall x y z. (forall w. R'(x,w) <=> R'(y,w)) /\
                    (forall w. R'(y,w) <=> R'(z,w))
                    ==> (forall w. R'(x,w) <=> R'(z,w)))|};;

  (* ------------------------------------------------------------------------- *)
  (* More auxiliary proofs for Brand's S and T modification.                   *)
  (* ------------------------------------------------------------------------- *)

  meson
   {%fol|(forall x y. R(x,y) <=> (forall z. R'(x,z) <=> R'(y,z))) /\
     (forall x. R'(x,x))
     ==> forall x y. ~R'(x,y) ==> ~R(x,y)|};;

  meson
   {%fol|(forall x y. R(x,y) <=> (forall z. R'(y,z) ==> R'(x,z))) /\
     (forall x. R'(x,x))
     ==> forall x y. ~R'(x,y) ==> ~R(x,y)|};;

  meson
   {%fol|(forall x y. R(x,y) <=> R'(x,y) /\ R'(y,x))
     ==> forall x y. ~R'(x,y) ==> ~R(x,y)|};;

  ***)
  [%expect {| |}]
;;
