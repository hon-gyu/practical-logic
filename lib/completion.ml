open Lib
open Formulas
open Fol
open Unif
open Equal
open Rewrite
open Order

(* Warnings the book's style trips in this file; the rest of the
   library compiles with them on.  See lib/dune. *)
[@@@warning "-8"]

(* ========================================================================= *)
(* Knuth-Bendix completion.                                                  *)
(*                                                                           *)
(* Copyright (c) 2003-2007, John Harrison. (See "LICENSE.txt" for details.)  *)
(* ========================================================================= *)

let renamepair (fm1,fm2) =
  let fvs1 = fv fm1 and fvs2 = fv fm2 in
  let nms1,nms2 = chop_list(length fvs1)
                           (map (fun n -> Var("x"^string_of_int n))
                                (0--(length fvs1 + length fvs2 - 1))) in
  subst (fpf fvs1 nms1) fm1,subst (fpf fvs2 nms2) fm2;;

(* ------------------------------------------------------------------------- *)
(* Rewrite (using unification) with l = r inside tm to give a critical pair. *)
(* ------------------------------------------------------------------------- *)

let rec listcases fn rfn lis acc =
  match lis with
    [] -> acc
  | h::t -> fn h (fun i h' -> rfn i (h'::t)) @
            listcases fn (fun i t' -> rfn i (h::t')) t acc;;

let rec overlaps (l,r) tm rfn =
  match tm with
    Fn(f,args) ->
        listcases (overlaps (l,r)) (fun i a -> rfn i (Fn(f,a))) args
                  (try [rfn (fullunify [l,tm]) r] with Failure _ -> [])
  | Var x -> [];;

(* ------------------------------------------------------------------------- *)
(* Generate all critical pairs between two equations.                        *)
(* ------------------------------------------------------------------------- *)

let crit1 (Atom(R("=",[l1;r1]))) (Atom(R("=",[l2;r2]))) =
  overlaps (l1,r1) l2 (fun i t -> subst i (mk_eq t r2));;

let critical_pairs fma fmb =
  let fm1,fm2 = renamepair (fma,fmb) in
  if fma = fmb then crit1 fm1 fm2
  else union (crit1 fm1 fm2) (crit1 fm2 fm1);;

(* ------------------------------------------------------------------------- *)
(* Simple example.                                                           *)
(* ------------------------------------------------------------------------- *)


(* ------------------------------------------------------------------------- *)
(* Orienting an equation.                                                    *)
(* ------------------------------------------------------------------------- *)

let normalize_and_orient ord eqs (Atom(R("=",[s;t]))) =
  let s' = rewrite eqs s and t' = rewrite eqs t in
  if ord s' t' then (s',t') else if ord t' s' then (t',s')
  else failwith "Can't orient equation";;

(* ------------------------------------------------------------------------- *)
(* Status report so the user doesn't get too bored.                          *)
(* ------------------------------------------------------------------------- *)

let status(eqs,def,crs) eqs0 =
  if eqs = eqs0 && (length crs) mod 1000 <> 0 then () else
  (print_string(string_of_int(length eqs)^" equations and "^
                string_of_int(length crs)^" pending critical pairs + "^
                string_of_int(length def)^" deferred");
   print_newline());;

(* ------------------------------------------------------------------------- *)
(* Completion main loop (deferring non-orientable equations).                *)
(* ------------------------------------------------------------------------- *)

let rec complete ord (eqs,def,crits) =
  match crits with
    eq::ocrits ->
        let trip =
          try let (s',t') = normalize_and_orient ord eqs eq in
              if s' = t' then (eqs,def,ocrits) else
              let eq' = Atom(R("=",[s';t'])) in
              let eqs' = eq'::eqs in
              eqs',def,
              ocrits @ itlist ((@) ** critical_pairs eq') eqs' []
          with Failure _ -> (eqs,eq::def,ocrits) in
        status trip eqs; complete ord trip
  | _ -> if def = [] then eqs else
         let e = find (can (normalize_and_orient ord eqs)) def in
         complete ord (eqs,subtract def [e],[e]);;

(* ------------------------------------------------------------------------- *)
(* A simple "manual" example, before considering packaging and refinements.  *)
(* ------------------------------------------------------------------------- *)


(* ------------------------------------------------------------------------- *)
(* Interreduction.                                                           *)
(* ------------------------------------------------------------------------- *)

let rec interreduce dun eqs =
  match eqs with
    (Atom(R("=",[l;r])))::oeqs ->
        let dun' = if rewrite (dun @ oeqs) l <> l then dun
                   else mk_eq l (rewrite (dun @ eqs) r)::dun in
        interreduce dun' oeqs
  | [] -> rev dun;;

(* ------------------------------------------------------------------------- *)
(* This does indeed help a lot.                                              *)
(* ------------------------------------------------------------------------- *)


(* ------------------------------------------------------------------------- *)
(* Overall function with post-simplification (but not dynamically).          *)
(* ------------------------------------------------------------------------- *)

let complete_and_simplify wts eqs =
  let ord = lpo_ge (weight wts) in
  let eqs' = map (fun e -> let l,r = normalize_and_orient ord [] e in
                           mk_eq l r) eqs in
  (interreduce [] ** complete ord)
  (eqs',[],unions(allpairs critical_pairs eqs' eqs'));;

(* ------------------------------------------------------------------------- *)
(* Inverse property (K&B example 4).                                         *)
(* ------------------------------------------------------------------------- *)


(* ------------------------------------------------------------------------- *)
(* The commutativity example (of course it fails...).                        *)
(* ------------------------------------------------------------------------- *)

(*******************

#trace complete;;

complete_and_simplify ["1"; "*"; "i"]
 [{%fol|(x * y) * z = x * (y * z)|};
  {%fol|1 * x = x|}; {%fol|x * 1 = x|}; {%fol|x * x = 1|}];;

 ********************)

(* ------------------------------------------------------------------------- *)
(* Central groupoids (K&B example 6).                                        *)
(* ------------------------------------------------------------------------- *)


(* ------------------------------------------------------------------------- *)
(* Step-by-step; note that we *do* deduce commutativity, deferred of course. *)
(* ------------------------------------------------------------------------- *)

let eqs =
 [{%fol|(x * y) * z = x * (y * z)|}; {%fol|1 * x = x|}; {%fol|x * 1 = x|}; {%fol|x * x = 1|}]
and wts = ["1"; "*"; "i"];;

let ord = lpo_ge (weight wts);;

let def = [] and crits = unions(allpairs critical_pairs eqs eqs);;
let complete1 ord (eqs,def,crits) =
  match crits with
    (eq::ocrits) ->
        let trip =
          try let (s',t') = normalize_and_orient ord eqs eq in
              if s' = t' then (eqs,def,ocrits) else
              let eq' = Atom(R("=",[s';t'])) in
              let eqs' = eq'::eqs in
              eqs',def,
              ocrits @ itlist ((@) ** critical_pairs eq') eqs' []
          with Failure _ -> (eqs,eq::def,ocrits) in
        status trip eqs; trip
  | _ -> if def = [] then (eqs,def,crits) else
         let e = find (can (normalize_and_orient ord eqs)) def in
         (eqs,subtract def [e],[e]);;


(* ------------------------------------------------------------------------- *)
(* Some of the exercises (these are taken from Baader & Nipkow).             *)
(* ------------------------------------------------------------------------- *)
