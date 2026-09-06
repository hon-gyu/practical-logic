open Lib
open Formulas
open Fol
open Equal
open Cooper
open Complex

(* Warnings the book's style trips in this file; the rest of the
   library compiles with them on.  See lib/dune. *)
[@@@warning "-8"]

(* ========================================================================= *)
(* Geometry theorem proving.                                                 *)
(*                                                                           *)
(* Copyright (c) 2003-2007, John Harrison. (See "LICENSE.txt" for details.)  *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* List of geometric properties with their coordinate translations.          *)
(* ------------------------------------------------------------------------- *)

let coordinations =
  ["collinear", (** Points 1, 2 and 3 lie on a common line **)
   {%fol|(1_x - 2_x) * (2_y - 3_y) = (1_y - 2_y) * (2_x - 3_x)|};
   "parallel", (** Lines (1,2) and (3,4) are parallel **)
    {%fol|(1_x - 2_x) * (3_y - 4_y) = (1_y - 2_y) * (3_x - 4_x)|};
   "perpendicular", (** Lines (1,2) and (3,4) are perpendicular **)
   {%fol|(1_x - 2_x) * (3_x - 4_x) + (1_y - 2_y) * (3_y - 4_y) = 0|};
   "lengths_eq", (** Lines (1,2) and (3,4) have the same length **)
   {%fol|(1_x - 2_x)^2 + (1_y - 2_y)^2 = (3_x - 4_x)^2 + (3_y - 4_y)^2|};
   "is_midpoint", (** Point 1 is the midpoint of line (2,3) **)
   {%fol|2 * 1_x = 2_x + 3_x /\ 2 * 1_y = 2_y + 3_y|};
   "is_intersection", (** Lines (2,3) and (4,5) meet at point 1 **)
   {%fol|(1_x - 2_x) * (2_y - 3_y) = (1_y - 2_y) * (2_x - 3_x) /\
     (1_x - 4_x) * (4_y - 5_y) = (1_y - 4_y) * (4_x - 5_x)|};
   "=", (** Points 1 and 2 are the same **)
   {%fol|(1_x = 2_x) /\ (1_y = 2_y)|}];;

(* ------------------------------------------------------------------------- *)
(* Convert formula into coordinate form.                                     *)
(* ------------------------------------------------------------------------- *)

let coordinate = onatoms
  (fun (R(a,args)) ->
    let xtms,ytms = unzip
     (map (fun (Var v) -> Var(v^"_x"),Var(v^"_y")) args) in
    let xs = map (fun n -> string_of_int n^"_x") (1--length args)
    and ys = map (fun n -> string_of_int n^"_y") (1--length args) in
    subst (fpf (xs @ ys) (xtms @ ytms)) (assoc a coordinations));;

(* ------------------------------------------------------------------------- *)
(* Trivial example.                                                          *)
(* ------------------------------------------------------------------------- *)


(* ------------------------------------------------------------------------- *)
(* Verify equivalence under rotation.                                        *)
(* ------------------------------------------------------------------------- *)

let invariant (x',y') ((s:string),z) =
  let m n f =
    let x = string_of_int n^"_x" and y = string_of_int n^"_y" in
    let i = fpf ["x";"y"] [Var x;Var y] in
    (x |-> tsubst i x') ((y |-> tsubst i y') f) in
  Iff(z,subst(itlist m (1--5) undefined) z);;

let invariant_under_translation = invariant ({%tm|x + X|},{%tm|y + Y|});;


let invariant_under_rotation fm =
  Imp({%fol|s^2 + c^2 = 1|},
      invariant ({%tm|c * x - s * y|},{%tm|s * x + c * y|}) fm);;


(* ------------------------------------------------------------------------- *)
(* And show we can always invent such a transformation to zero a y:          *)
(* ------------------------------------------------------------------------- *)


(* ------------------------------------------------------------------------- *)
(* Choose one point to be the origin and rotate to zero another y coordinate *)
(* ------------------------------------------------------------------------- *)

let originate fm =
  let a::b::ovs = fv fm in
  subst (fpf [a^"_x"; a^"_y"; b^"_y"] [zero; zero; zero])
        (coordinate fm);;

(* ------------------------------------------------------------------------- *)
(* Other interesting invariances.                                            *)
(* ------------------------------------------------------------------------- *)

let invariant_under_scaling fm =
  Imp({%fol|~(A = 0)|},invariant({%tm|A * x|},{%tm|A * y|}) fm);;

let invariant_under_shearing = invariant({%tm|x + b * y|},{%tm|y|});;


(* ------------------------------------------------------------------------- *)
(* One from "Algorithms for Computer Algebra"                                *)
(* ------------------------------------------------------------------------- *)


(* ------------------------------------------------------------------------- *)
(* Reduce p using triangular set, collecting degenerate conditions.          *)
(* ------------------------------------------------------------------------- *)

let rec pprove vars triang p degens =
  if p = zero then degens else
  match triang with
    [] -> (mk_eq p zero)::degens
  | (Fn("+",[c;Fn("*",[Var x;_])]) as q)::qs ->
        if x <> hd vars then
          if mem (hd vars) (fvt p)
          then itlist (pprove vars triang) (coefficients vars p) degens
          else pprove (tl vars) triang p degens
        else
          let k,p' = pdivide vars p q in
          if k = 0 then pprove vars qs p' degens else
          let degens' = Not(mk_eq (head vars q) zero)::degens in
          itlist (pprove vars qs) (coefficients vars p') degens';;

(* ------------------------------------------------------------------------- *)
(* Triangulate a set of polynomials.                                         *)
(* ------------------------------------------------------------------------- *)

let rec triangulate vars consts pols =
  if vars = [] then pols else
  let cns,tpols = partition (is_constant vars) pols in
  if cns <> [] then triangulate vars (cns @ consts) tpols else
  if length pols <= 1 then pols @ triangulate (tl vars) [] consts else
  let n = end_itlist min (map (degree vars) pols) in
  let p = find (fun p -> degree vars p = n) pols in
  let ps = subtract pols [p] in
  triangulate vars consts (p::map (fun q -> snd(pdivide vars q p)) ps);;

(* ------------------------------------------------------------------------- *)
(* Trivial version of Wu's method based on repeated pseudo-division.         *)
(* ------------------------------------------------------------------------- *)

let wu fm vars zeros =
  let gfm0 = coordinate fm in
  let gfm = subst(itlist (fun v -> v |-> zero) zeros undefined) gfm0 in
  if not (set_eq vars (fv gfm)) then failwith "wu: bad parameters" else
  let ant,con = dest_imp gfm in
  let pols = map (lhs ** polyatom vars) (conjuncts ant)
  and ps = map (lhs ** polyatom vars) (conjuncts con) in
  let tri = triangulate vars [] pols in
  itlist (fun p -> union(pprove vars tri p [])) ps [];;

(* ------------------------------------------------------------------------- *)
(* Simson's theorem.                                                         *)
(* ------------------------------------------------------------------------- *)


(*** Other examples removed from text

(* ------------------------------------------------------------------------- *)
(* Centroid (Chou, example 142).                                             *)
(* ------------------------------------------------------------------------- *)

(grobner_decide ** originate)
 {%fol|is_midpoint(d,b,c) /\ is_midpoint(e,a,c) /\
   is_midpoint(f,a,b) /\ is_intersection(m,b,e,a,d)
   ==> collinear(c,f,m)|};;

****)
