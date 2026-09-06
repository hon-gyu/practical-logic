open Lib
open Formulas
open Prop
open Fol
open Skolem
open Unif
open Tableaux

(* Warnings the book's style trips in this file; the rest of the
   library compiles with them on.  See lib/dune. *)
[@@@warning "-32-39"]

(* ========================================================================= *)
(* Resolution.                                                               *)
(*                                                                           *)
(* Copyright (c) 2003-2007, John Harrison. (See "LICENSE.txt" for details.)  *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Barber's paradox is an example of why we need factoring.                  *)
(* ------------------------------------------------------------------------- *)

let barb = {%fol|~(exists b. forall x. shaves(b,x) <=> ~shaves(x,x))|};;


(* ------------------------------------------------------------------------- *)
(* MGU of a set of literals.                                                 *)
(* ------------------------------------------------------------------------- *)

let rec mgu l env =
  match l with
    a::b::rest -> mgu (b::rest) (unify_literals env (a,b))
  | _ -> solve env;;

let unifiable p q = can (unify_literals undefined) (p,q);;

(* ------------------------------------------------------------------------- *)
(* Rename a clause.                                                          *)
(* ------------------------------------------------------------------------- *)

let rename pfx cls =
  let fvs = fv(list_disj cls) in
  let vvs = map (fun s -> Var(pfx^s)) fvs  in
  map (subst(fpf fvs vvs)) cls;;

(* ------------------------------------------------------------------------- *)
(* General resolution rule, incorporating factoring as in Robinson's paper.  *)
(* ------------------------------------------------------------------------- *)

let resolvents cl1 cl2 p acc =
  let ps2 = filter (unifiable(negate p)) cl2 in
  if ps2 = [] then acc else
  let ps1 = filter (fun q -> q <> p && unifiable p q) cl1 in
  let pairs = allpairs (fun s1 s2 -> s1,s2)
                       (map (fun pl -> p::pl) (allsubsets ps1))
                       (allnonemptysubsets ps2) in
  itlist (fun (s1,s2) sof ->
           try image (subst (mgu (s1 @ map negate s2) undefined))
                     (union (subtract cl1 s1) (subtract cl2 s2)) :: sof
           with Failure _ -> sof) pairs acc;;

let resolve_clauses cls1 cls2 =
  let cls1' = rename "x" cls1 and cls2' = rename "y" cls2 in
  itlist (resolvents cls1' cls2') cls1' [];;

(* ------------------------------------------------------------------------- *)
(* Basic "Argonne" loop.                                                     *)
(* ------------------------------------------------------------------------- *)

let rec resloop (used,unused) =
  match unused with
    [] -> failwith "No proof found"
  | cl::ros ->
      print_string(string_of_int(length used) ^ " used; "^
                   string_of_int(length unused) ^ " unused.");
      print_newline();
      let used' = insert cl used in
      let news = itlist(@) (mapfilter (resolve_clauses cl) used') [] in
      if mem [] news then true else resloop (used',ros@news);;

let pure_resolution fm = resloop([],simpcnf(specialize(pnf fm)));;

let resolution fm =
  let fm1 = askolemize(Not(generalize fm)) in
  map (pure_resolution ** list_conj) (simpdnf fm1);;

(* ------------------------------------------------------------------------- *)
(* Simple example that works well.                                           *)
(* ------------------------------------------------------------------------- *)


(* ------------------------------------------------------------------------- *)
(* Matching of terms and literals.                                           *)
(* ------------------------------------------------------------------------- *)

let rec term_match env eqs =
  match eqs with
    [] -> env
  | (Fn(f,fa),Fn(g,ga))::oth when f = g && length fa = length ga ->
        term_match env (zip fa ga @ oth)
  | (Var x,t)::oth ->
        if not (defined env x) then term_match ((x |-> t) env) oth
        else if apply env x = t then term_match env oth
        else failwith "term_match"
  | _ -> failwith "term_match";;

let rec match_literals env tmp =
  match tmp with
    Atom(R(p,a1)),Atom(R(q,a2)) | Not(Atom(R(p,a1))),Not(Atom(R(q,a2))) ->
       term_match env [Fn(p,a1),Fn(q,a2)]
  | _ -> failwith "match_literals";;

(* ------------------------------------------------------------------------- *)
(* Test for subsumption                                                      *)
(* ------------------------------------------------------------------------- *)

let subsumes_clause cls1 cls2 =
  let rec subsume env cls =
    match cls with
      [] -> env
    | l1::clt ->
        tryfind (fun l2 -> subsume (match_literals env (l1,l2)) clt)
                cls2 in
  can (subsume undefined) cls1;;

(* ------------------------------------------------------------------------- *)
(* With deletion of tautologies and bi-subsumption with "unused".            *)
(* ------------------------------------------------------------------------- *)

let rec replace cl lis =
  match lis with
    [] -> [cl]
  | c::cls -> if subsumes_clause cl c then cl::cls
              else c::(replace cl cls);;

let incorporate gcl cl unused =
  if trivial cl ||
     exists (fun c -> subsumes_clause c cl) (gcl::unused)
  then unused else replace cl unused;;

let rec resloop (used,unused) =
  match unused with
    [] -> failwith "No proof found"
  | cl::ros ->
      print_string(string_of_int(length used) ^ " used; "^
                   string_of_int(length unused) ^ " unused.");
      print_newline();
      let used' = insert cl used in
      let news = itlist(@) (mapfilter (resolve_clauses cl) used') [] in
      if mem [] news then true
      else resloop(used',itlist (incorporate cl) news ros);;

let pure_resolution fm = resloop([],simpcnf(specialize(pnf fm)));;

let resolution fm =
  let fm1 = askolemize(Not(generalize fm)) in
  map (pure_resolution ** list_conj) (simpdnf fm1);;

(* ------------------------------------------------------------------------- *)
(* This is now a lot quicker.                                                *)
(* ------------------------------------------------------------------------- *)


(* ------------------------------------------------------------------------- *)
(* Positive (P1) resolution.                                                 *)
(* ------------------------------------------------------------------------- *)

let presolve_clauses cls1 cls2 =
  if forall positive cls1 || forall positive cls2
  then resolve_clauses cls1 cls2 else [];;

let rec presloop (used,unused) =
  match unused with
    [] -> failwith "No proof found"
  | cl::ros ->
      print_string(string_of_int(length used) ^ " used; "^
                   string_of_int(length unused) ^ " unused.");
      print_newline();
      let used' = insert cl used in
      let news = itlist(@) (mapfilter (presolve_clauses cl) used') [] in
      if mem [] news then true else
      presloop(used',itlist (incorporate cl) news ros);;

let pure_presolution fm = presloop([],simpcnf(specialize(pnf fm)));;

let presolution fm =
  let fm1 = askolemize(Not(generalize fm)) in
  map (pure_presolution ** list_conj) (simpdnf fm1);;

(* ------------------------------------------------------------------------- *)
(* Example: the (in)famous Los problem.                                      *)
(* ------------------------------------------------------------------------- *)


(* ------------------------------------------------------------------------- *)
(* Example                                                                   *)
(* ------------------------------------------------------------------------- *)
