open Lib
open Formulas
open Prop
open Fol
open Skolem
open Equal
open Qelim
open Cooper

(* Warnings the book's style trips in this file; the rest of the
   library compiles with them on.  See lib/dune. *)
[@@@warning "-8-39-52"]

(* ========================================================================= *)
(* Complex quantifier elimination (by simple divisibility a la Tarski).      *)
(*                                                                           *)
(* Copyright (c) 2003-2007, John Harrison. (See "LICENSE.txt" for details.)  *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Basic arithmetic operations on canonical polynomials.                     *)
(* ------------------------------------------------------------------------- *)

let rec poly_add vars pol1 pol2 =
  match (pol1,pol2) with
   (Fn("+",[c; Fn("*",[Var x; p])]),Fn("+",[d; Fn("*",[Var y; q])])) ->
        if earlier vars x y then poly_ladd vars pol2 pol1
        else if earlier vars y x then poly_ladd vars pol1 pol2 else
        let e = poly_add vars c d and r = poly_add vars p q in
        if r = zero then e else Fn("+",[e; Fn("*",[Var x; r])])
    | (_,Fn("+",_)) -> poly_ladd vars pol1 pol2
    | (Fn("+",_),pol2) -> poly_ladd vars pol2 pol1
    | _ -> numeral2 (+/) pol1 pol2
and poly_ladd vars =
  fun pol1 (Fn("+",[d; Fn("*",[Var y; q])])) ->
        Fn("+",[poly_add vars pol1 d; Fn("*",[Var y; q])]);;

let rec poly_neg =
  function (Fn("+",[c; Fn("*",[Var x; p])])) ->
                Fn("+",[poly_neg c; Fn("*",[Var x; poly_neg p])])
         | n -> numeral1 minus_num n;;

let poly_sub vars p q = poly_add vars p (poly_neg q);;

let rec poly_mul vars pol1 pol2 =
  match (pol1,pol2) with
   (Fn("+",[c; Fn("*",[Var x; p])]),Fn("+",[d; Fn("*",[Var y; q])])) ->
        if earlier vars x y then poly_lmul vars pol2 pol1
        else poly_lmul vars pol1 pol2
  | (Fn("0",[]),_) | (_,Fn("0",[])) -> zero
  | (_,Fn("+",_)) -> poly_lmul vars pol1 pol2
  | (Fn("+",_),_) -> poly_lmul vars pol2 pol1
  | _ -> numeral2 ( */ ) pol1 pol2
and poly_lmul vars =
  fun pol1 (Fn("+",[d; Fn("*",[Var y; q])])) ->
        poly_add vars (poly_mul vars pol1 d)
                     (Fn("+",[zero;
                              Fn("*",[Var y; poly_mul vars pol1 q])]));;

let poly_pow vars p n = funpow n (poly_mul vars p) (Fn("1",[]));;

let poly_div vars p q = poly_mul vars p (numeral1((//) (Int 1)) q);;

let poly_var x = Fn("+",[zero; Fn("*",[Var x; Fn("1",[])])]);;

(* ------------------------------------------------------------------------- *)
(* Convert term into canonical polynomial representative.                    *)
(* ------------------------------------------------------------------------- *)

let rec polynate vars tm =
  match tm with
    Var x -> poly_var x
  | Fn("-",[t]) -> poly_neg (polynate vars t)
  | Fn("+",[s;t]) -> poly_add vars (polynate vars s) (polynate vars t)
  | Fn("-",[s;t]) -> poly_sub vars (polynate vars s) (polynate vars t)
  | Fn("*",[s;t]) -> poly_mul vars (polynate vars s) (polynate vars t)
  | Fn("/",[s;t]) -> poly_div vars (polynate vars s) (polynate vars t)
  | Fn("^",[p;Fn(n,[])]) ->
                     poly_pow vars (polynate vars p) (int_of_string n)
  | _ -> if is_numeral tm then tm else failwith "lint: unknown term";;

(* ------------------------------------------------------------------------- *)
(* Do likewise for atom so the RHS is zero.                                  *)
(* ------------------------------------------------------------------------- *)

let polyatom vars fm =
  match fm with
    Atom(R(a,[s;t])) -> Atom(R(a,[polynate vars (Fn("-",[s;t]));zero]))
  | _ -> failwith "polyatom: not an atom";;

(* ------------------------------------------------------------------------- *)
(* Sanity check.                                                             *)
(* ------------------------------------------------------------------------- *)


(* ------------------------------------------------------------------------- *)
(* Useful utility functions for polynomial terms.                            *)
(* ------------------------------------------------------------------------- *)

let rec coefficients vars =
  function Fn("+",[c; Fn("*",[Var x; q])]) when x = hd vars ->
                c::(coefficients vars q)
         | p -> [p];;

let degree vars p = length(coefficients vars p) - 1;;

let is_constant vars p = degree vars p = 0;;

let head vars p = last(coefficients vars p);;

let rec behead vars =
  function Fn("+",[c; Fn("*",[Var x; p])]) when x = hd vars ->
        let p' = behead vars p in
        if p' = zero then c else Fn("+",[c; Fn("*",[Var x; p'])])
  | _ -> zero;;

(* ------------------------------------------------------------------------- *)
(* Get the constant multiple of the "maximal" monomial (implicit lex order)  *)
(* ------------------------------------------------------------------------- *)

let rec poly_cmul k p =
  match p with
    Fn("+",[c; Fn("*",[Var x; q])]) ->
        Fn("+",[poly_cmul k c; Fn("*",[Var x; poly_cmul k q])])
  | _ -> numeral1 (fun m -> k */ m) p;;

let rec headconst p =
  match p with
    Fn("+",[c; Fn("*",[Var x; q])]) -> headconst q
  | Fn(n,[]) -> dest_numeral p;;

(* ------------------------------------------------------------------------- *)
(* Make a polynomial monic and return negativity flag for head constant      *)
(* ------------------------------------------------------------------------- *)

let monic p =
  let h = headconst p in
  if h =/ Int 0 then p,false else poly_cmul (Int 1 // h) p,h </ Int 0;;

(* ------------------------------------------------------------------------- *)
(* Pseudo-division of s by p; head coefficient of p assumed nonzero.         *)
(* Returns (k,r) so that a^k s = p q + r for some q, deg(r) < deg(p).        *)
(* Optimized only for the trivial case of equal head coefficients; no GCDs.  *)
(* ------------------------------------------------------------------------- *)

let pdivide =
  let shift1 x p = Fn("+",[zero; Fn("*",[Var x; p])]) in
  let rec pdivide_aux vars a n p k s =
    if s = zero then (k,s) else
    let b = head vars s and m = degree vars s in
    if m < n then (k,s) else
    let p' = funpow (m - n) (shift1 (hd vars)) p in
    if a = b then pdivide_aux vars a n p k (poly_sub vars s p')
    else pdivide_aux vars a n p (k+1)
          (poly_sub vars (poly_mul vars a s) (poly_mul vars b p')) in
  fun vars s p -> pdivide_aux vars (head vars p) (degree vars p) p 0 s;;

(* ------------------------------------------------------------------------- *)
(* Datatype of signs.                                                        *)
(* ------------------------------------------------------------------------- *)

type sign = Zero | Nonzero | Positive | Negative;;

let swap swf s =
  if not swf then s else
  match s with
    Positive -> Negative
  | Negative -> Positive
  | _ -> s;;

(* ------------------------------------------------------------------------- *)
(* Lookup and asserting of polynomial sign, modulo constant multiples.       *)
(* Note that we are building in a characteristic-zero assumption here.       *)
(* ------------------------------------------------------------------------- *)

let findsign sgns p =
  try let p',swf = monic p in swap swf (assoc p' sgns)
  with Failure _ -> failwith "findsign";;

let assertsign sgns (p,s) =
  if p = zero then if s = Zero then sgns else failwith "assertsign" else
  let p',swf = monic p in
  let s' = swap swf s in
  let s0 = try assoc p' sgns with Failure _ -> s' in
  if s' = s0 || s0 = Nonzero && (s' = Positive || s' = Negative)
  then (p',s')::(subtract sgns [p',s0]) else failwith "assertsign";;

(* ------------------------------------------------------------------------- *)
(* Deduce or case-split over zero status of polynomial.                      *)
(* ------------------------------------------------------------------------- *)

let split_zero sgns pol cont_z cont_n =
  try let z = findsign sgns pol in
      (if z = Zero then cont_z else cont_n) sgns
  with Failure "findsign" ->
      let eq = Atom(R("=",[pol; zero])) in
      Or(And(eq,cont_z (assertsign sgns (pol,Zero))),
         And(Not eq,cont_n (assertsign sgns (pol,Nonzero))));;

(* ------------------------------------------------------------------------- *)
(* Whether a polynomial is nonzero in a context.                             *)
(* ------------------------------------------------------------------------- *)

let poly_nonzero vars sgns pol =
  let cs = coefficients vars pol in
  let dcs,ucs = partition (can (findsign sgns)) cs in
  if exists (fun p -> findsign sgns p <> Zero) dcs then True
  else if ucs = [] then False else
  end_itlist mk_or (map (fun p -> Not(mk_eq p zero)) ucs);;

(* ------------------------------------------------------------------------- *)
(* Non-divisibility of q by p.                                               *)
(* ------------------------------------------------------------------------- *)

let rec poly_nondiv vars sgns p s =
  let _,r = pdivide vars s p in poly_nonzero vars sgns r;;

(* ------------------------------------------------------------------------- *)
(* Main reduction for exists x. all eqs = 0 and all neqs =/= 0, in context.  *)
(* ------------------------------------------------------------------------- *)

let rec cqelim vars (eqs,neqs) sgns =
  try let c = find (is_constant vars) eqs in
     (try let sgns' = assertsign sgns (c,Zero)
          and eqs' = subtract eqs [c] in
          And(mk_eq c zero,cqelim vars (eqs',neqs) sgns')
      with Failure "assertsign" -> False)
  with Failure _ ->
     if eqs = [] then list_conj(map (poly_nonzero vars sgns) neqs) else
     let n = end_itlist min (map (degree vars) eqs) in
     let p = find (fun p -> degree vars p = n) eqs in
     let oeqs = subtract eqs [p] in
     split_zero sgns (head vars p)
       (cqelim vars (behead vars p::oeqs,neqs))
       (fun sgns' ->
          let cfn s = snd(pdivide vars s p) in
          if oeqs <> [] then cqelim vars (p::(map cfn oeqs),neqs) sgns'
          else if neqs = [] then True else
          let q = end_itlist (poly_mul vars) neqs in
          poly_nondiv vars sgns' p (poly_pow vars q (degree vars p)));;

(* ------------------------------------------------------------------------- *)
(* Basic complex quantifier elimination on actual existential formula.       *)
(* ------------------------------------------------------------------------- *)

let init_sgns = [Fn("1",[]),Positive; Fn("0",[]),Zero];;

let basic_complex_qelim vars (Exists(x,p)) =
  let eqs,neqs = partition (non negative) (conjuncts p) in
  cqelim (x::vars) (map lhs eqs,map (lhs ** negate) neqs) init_sgns;;

(* ------------------------------------------------------------------------- *)
(* Full quantifier elimination.                                              *)
(* ------------------------------------------------------------------------- *)

let complex_qelim =
  simplify ** evalc **
  lift_qelim polyatom (dnf ** cnnf (fun x -> x) ** evalc)
             basic_complex_qelim;;

(* ------------------------------------------------------------------------- *)
(* Examples.                                                                 *)
(* ------------------------------------------------------------------------- *)
