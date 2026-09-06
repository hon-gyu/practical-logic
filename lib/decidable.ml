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


(* ------------------------------------------------------------------------- *)
(* Show how we need to do PNF transformation with care.                      *)
(* ------------------------------------------------------------------------- *)


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

(* ------------------------------------------------------------------------- *)
(* Examples.                                                                 *)
(* ------------------------------------------------------------------------- *)


(* ------------------------------------------------------------------------- *)
(* Stronger version of "aedecide" similar to Wang's classic procedure.       *)
(* ------------------------------------------------------------------------- *)

let wang fm = aedecide(miniscope(nnf(simplify fm)));;

(* ------------------------------------------------------------------------- *)
(* It works well on simple monadic formulas.                                 *)
(* ------------------------------------------------------------------------- *)


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


(* ------------------------------------------------------------------------- *)
(* We can "fix" the traditional list by assuming nonemptiness.               *)
(* ------------------------------------------------------------------------- *)

let all_possible_syllogisms' =
  let p =
    {%fol|(exists x. P(x)) /\ (exists x. M(x)) /\ (exists x. S(x))|} in
  map (fun t -> Imp(p,t)) all_possible_syllogisms;;


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

(* ------------------------------------------------------------------------- *)
(* Example.                                                                  *)
(* ------------------------------------------------------------------------- *)


(* ------------------------------------------------------------------------- *)
(* Little auxiliary results for failure of finite model property.            *)
(* ------------------------------------------------------------------------- *)
