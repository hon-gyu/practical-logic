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

(* ------------------------------------------------------------------------- *)
(* Example of naivety of tableau prover.                                     *)
(* ------------------------------------------------------------------------- *)


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

(* ------------------------------------------------------------------------- *)
(* Example.                                                                  *)
(* ------------------------------------------------------------------------- *)


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
