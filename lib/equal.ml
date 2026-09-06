open Lib
open Formulas
open Fol
open Skolem

(* Warnings the book's style trips in this file; the rest of the
   library compiles with them on.  See lib/dune. *)
[@@@warning "-39"]

(* ========================================================================= *)
(* First order logic with equality.                                          *)
(*                                                                           *)
(* Copyright (c) 2003-2007, John Harrison. (See "LICENSE.txt" for details.)  *)
(* ========================================================================= *)

let is_eq = function (Atom(R("=",_))) -> true | _ -> false;;

let mk_eq s t = Atom(R("=",[s;t]));;

let dest_eq fm =
  match fm with
    Atom(R("=",[s;t])) -> s,t
  | _ -> failwith "dest_eq: not an equation";;

let lhs eq = fst(dest_eq eq) and rhs eq = snd(dest_eq eq);;

(* ------------------------------------------------------------------------- *)
(* The set of predicates in a formula.                                       *)
(* ------------------------------------------------------------------------- *)

let rec predicates fm = atom_union (fun (R(p,a)) -> [p,length a]) fm;;

(* ------------------------------------------------------------------------- *)
(* Code to generate equality axioms for functions.                           *)
(* ------------------------------------------------------------------------- *)

let function_congruence (f,n) =
  if n = 0 then [] else
  let argnames_x = map (fun n -> "x"^(string_of_int n)) (1 -- n)
  and argnames_y = map (fun n -> "y"^(string_of_int n)) (1 -- n) in
  let args_x = map (fun x -> Var x) argnames_x
  and args_y = map (fun x -> Var x) argnames_y in
  let ant = end_itlist mk_and (map2 mk_eq args_x args_y)
  and con = mk_eq (Fn(f,args_x)) (Fn(f,args_y)) in
  [itlist mk_forall (argnames_x @ argnames_y) (Imp(ant,con))];;

(* ------------------------------------------------------------------------- *)
(* Example.                                                                  *)
(* ------------------------------------------------------------------------- *)


(* ------------------------------------------------------------------------- *)
(* And for predicates.                                                       *)
(* ------------------------------------------------------------------------- *)

let predicate_congruence (p,n) =
  if n = 0 then [] else
  let argnames_x = map (fun n -> "x"^(string_of_int n)) (1 -- n)
  and argnames_y = map (fun n -> "y"^(string_of_int n)) (1 -- n) in
  let args_x = map (fun x -> Var x) argnames_x
  and args_y = map (fun x -> Var x) argnames_y in
  let ant = end_itlist mk_and (map2 mk_eq args_x args_y)
  and con = Imp(Atom(R(p,args_x)),Atom(R(p,args_y))) in
  [itlist mk_forall (argnames_x @ argnames_y) (Imp(ant,con))];;

(* ------------------------------------------------------------------------- *)
(* Hence implement logic with equality just by adding equality "axioms".     *)
(* ------------------------------------------------------------------------- *)

let equivalence_axioms =
  [{%fol|forall x. x = x|}; {%fol|forall x y z. x = y /\ x = z ==> y = z|}];;

let equalitize fm =
  let allpreds = predicates fm in
  if not (mem ("=",2) allpreds) then fm else
  let preds = subtract allpreds ["=",2] and funcs = functions fm in
  let axioms = itlist (union ** function_congruence) funcs
                      (itlist (union ** predicate_congruence) preds
                              equivalence_axioms) in
  Imp(end_itlist mk_and axioms,fm);;

(* ------------------------------------------------------------------------- *)
(* A simple example (see EWD1266a and the application to Morley's theorem).  *)
(* ------------------------------------------------------------------------- *)
