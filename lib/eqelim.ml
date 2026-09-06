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

(* ------------------------------------------------------------------------- *)
(* Examples.                                                                 *)
(* ------------------------------------------------------------------------- *)


(* ------------------------------------------------------------------------- *)
(* Older stuff not now in the text.                                          *)
(* ------------------------------------------------------------------------- *)
