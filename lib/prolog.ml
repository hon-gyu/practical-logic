open Lib
open Intro
open Formulas
open Prop
open Fol
open Skolem
open Unif
open Tableaux

(* Warnings the book's style trips in this file; the rest of the
   library compiles with them on.  See lib/dune. *)
[@@@warning "-41"]

(* ========================================================================= *)
(* Backchaining procedure for Horn clauses, and toy Prolog implementation.   *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Rename a rule.                                                            *)
(* ------------------------------------------------------------------------- *)

let renamerule k (asm,c) =
  let fvs = fv(list_conj(c::asm)) in
  let n = length fvs in
  let vvs = map (fun i -> "_" ^ string_of_int i) (k -- (k+n-1)) in
  let inst = subst(fpf fvs (map (fun x -> Var x) vvs)) in
  (map inst asm,inst c),k+n;;

(* ------------------------------------------------------------------------- *)
(* Basic prover for Horn clauses based on backchaining with unification.     *)
(* ------------------------------------------------------------------------- *)

let rec backchain rules n k env goals =
  match goals with
    [] -> env
  | g::gs ->
     if n = 0 then failwith "Too deep" else
     tryfind (fun rule ->
        let (a,c),k' = renamerule k rule in
        backchain rules (n - 1) k' (unify_literals env (c,g)) (a @ gs))
     rules;;

let hornify cls =
  let pos,neg = partition positive cls in
  if length pos > 1 then failwith "non-Horn clause"
  else (map negate neg,if pos = [] then False else hd pos);;

let hornprove fm =
  let rules = map hornify (simpcnf(skolemize(Not(generalize fm)))) in
  deepen (fun n -> backchain rules n 0 undefined [False],n) 0;;

(* ------------------------------------------------------------------------- *)
(* A Horn example.                                                           *)
(* ------------------------------------------------------------------------- *)


(* ------------------------------------------------------------------------- *)
(* Parsing rules in a Prolog-like syntax.                                    *)
(* ------------------------------------------------------------------------- *)

let parserule s =
  let c,rest =
    parse_formula (parse_infix_atom,parse_atom) [] (lex(explode s)) in
  let asm,rest1 =
    if rest <> [] && hd rest = ":-"
    then parse_list ","
          (parse_formula (parse_infix_atom,parse_atom) []) (tl rest)
    else [],rest in
  if rest1 = [] then (asm,c) else failwith "Extra material after rule";;

(* ------------------------------------------------------------------------- *)
(* Prolog interpreter: just use depth-first search not iterative deepening.  *)
(* ------------------------------------------------------------------------- *)

let simpleprolog rules gl =
  backchain (map parserule rules) (-1) 0 undefined [parse_fol_formula gl];;

(* ------------------------------------------------------------------------- *)
(* Ordering example.                                                         *)
(* ------------------------------------------------------------------------- *)


(* ------------------------------------------------------------------------- *)
(* With instantiation collection to produce a more readable result.          *)
(* ------------------------------------------------------------------------- *)

let prolog rules gl =
  let i = solve(simpleprolog rules gl) in
  mapfilter (fun x -> Atom(R("=",[Var x; apply i x]))) (fv(parse_fol_formula gl));;

(* ------------------------------------------------------------------------- *)
(* Example again.                                                            *)
(* ------------------------------------------------------------------------- *)
