open Lib
open Formulas
open Fol
open Equal
open Cooper
open Complex
open Real
open Grobner

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


let%expect_test "eg: Trivial example" =
  print_fol_formula
    (coordinate {%fol|collinear(a,b,c) ==> collinear(b,a,c)|});
  [%expect {|
    <<(a_x - b_x) * (b_y - c_y) = (a_y - b_y) * (b_x - c_x) ==> (b_x - a_x) *
      (a_y - c_y) = (b_y - a_y) * (a_x - c_x)>>
    |}]
;;

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

let%expect_test _ =
  print_bool
    (forall (grobner_decide ** invariant_under_translation) coordinations);
  [%expect {|
    2 basis elements and 1 pairs
    2 basis elements and 1 pairs
    2 basis elements and 1 pairs
    2 basis elements and 1 pairs
    2 basis elements and 1 pairs
    2 basis elements and 1 pairs
    2 basis elements and 1 pairs
    2 basis elements and 1 pairs
    3 basis elements and 3 pairs
    3 basis elements and 2 pairs
    3 basis elements and 3 pairs
    3 basis elements and 2 pairs
    4 basis elements and 4 pairs
    3 basis elements and 3 pairs
    3 basis elements and 2 pairs
    3 basis elements and 3 pairs
    3 basis elements and 2 pairs
    4 basis elements and 4 pairs
    3 basis elements and 3 pairs
    3 basis elements and 2 pairs
    3 basis elements and 3 pairs
    3 basis elements and 2 pairs
    4 basis elements and 4 pairs
    3 basis elements and 3 pairs
    3 basis elements and 2 pairs
    3 basis elements and 3 pairs
    3 basis elements and 2 pairs
    4 basis elements and 4 pairs
    3 basis elements and 3 pairs
    3 basis elements and 2 pairs
    3 basis elements and 3 pairs
    3 basis elements and 2 pairs
    4 basis elements and 4 pairs
    3 basis elements and 3 pairs
    3 basis elements and 2 pairs
    3 basis elements and 3 pairs
    3 basis elements and 2 pairs
    4 basis elements and 4 pairs
    true
    |}]
;;


let invariant_under_rotation fm =
  Imp({%fol|s^2 + c^2 = 1|},
      invariant ({%tm|c * x - s * y|},{%tm|s * x + c * y|}) fm);;


let%expect_test _ =
  print_bool
    (forall (grobner_decide ** invariant_under_rotation) coordinations);
  [%expect {|
    3 basis elements and 3 pairs
    3 basis elements and 2 pairs
    3 basis elements and 3 pairs
    4 basis elements and 5 pairs
    5 basis elements and 8 pairs
    5 basis elements and 7 pairs
    5 basis elements and 6 pairs
    5 basis elements and 5 pairs
    3 basis elements and 3 pairs
    3 basis elements and 2 pairs
    3 basis elements and 3 pairs
    4 basis elements and 5 pairs
    5 basis elements and 8 pairs
    5 basis elements and 7 pairs
    5 basis elements and 6 pairs
    5 basis elements and 5 pairs
    3 basis elements and 3 pairs
    3 basis elements and 2 pairs
    3 basis elements and 3 pairs
    4 basis elements and 5 pairs
    5 basis elements and 8 pairs
    5 basis elements and 7 pairs
    5 basis elements and 6 pairs
    5 basis elements and 5 pairs
    3 basis elements and 3 pairs
    3 basis elements and 2 pairs
    3 basis elements and 3 pairs
    4 basis elements and 5 pairs
    5 basis elements and 8 pairs
    5 basis elements and 7 pairs
    5 basis elements and 6 pairs
    5 basis elements and 5 pairs
    4 basis elements and 6 pairs
    4 basis elements and 5 pairs
    4 basis elements and 4 pairs
    5 basis elements and 7 pairs
    5 basis elements and 6 pairs
    4 basis elements and 6 pairs
    4 basis elements and 5 pairs
    4 basis elements and 4 pairs
    5 basis elements and 7 pairs
    5 basis elements and 6 pairs
    4 basis elements and 6 pairs
    5 basis elements and 9 pairs
    5 basis elements and 8 pairs
    6 basis elements and 12 pairs
    7 basis elements and 17 pairs
    8 basis elements and 23 pairs
    9 basis elements and 30 pairs
    9 basis elements and 29 pairs
    9 basis elements and 28 pairs
    9 basis elements and 27 pairs
    4 basis elements and 6 pairs
    5 basis elements and 9 pairs
    5 basis elements and 8 pairs
    6 basis elements and 12 pairs
    7 basis elements and 17 pairs
    8 basis elements and 23 pairs
    9 basis elements and 30 pairs
    9 basis elements and 29 pairs
    9 basis elements and 28 pairs
    10 basis elements and 36 pairs
    10 basis elements and 35 pairs
    10 basis elements and 34 pairs
    10 basis elements and 33 pairs
    10 basis elements and 32 pairs
    10 basis elements and 31 pairs
    10 basis elements and 30 pairs
    10 basis elements and 29 pairs
    10 basis elements and 28 pairs
    10 basis elements and 27 pairs
    10 basis elements and 26 pairs
    11 basis elements and 35 pairs
    4 basis elements and 6 pairs
    4 basis elements and 5 pairs
    4 basis elements and 4 pairs
    4 basis elements and 6 pairs
    4 basis elements and 5 pairs
    4 basis elements and 4 pairs
    5 basis elements and 7 pairs
    5 basis elements and 6 pairs
    4 basis elements and 6 pairs
    4 basis elements and 5 pairs
    5 basis elements and 8 pairs
    6 basis elements and 12 pairs
    7 basis elements and 17 pairs
    7 basis elements and 16 pairs
    7 basis elements and 15 pairs
    7 basis elements and 14 pairs
    7 basis elements and 13 pairs
    7 basis elements and 12 pairs
    4 basis elements and 6 pairs
    4 basis elements and 5 pairs
    5 basis elements and 8 pairs
    6 basis elements and 12 pairs
    7 basis elements and 17 pairs
    8 basis elements and 23 pairs
    8 basis elements and 22 pairs
    8 basis elements and 21 pairs
    8 basis elements and 20 pairs
    8 basis elements and 19 pairs
    8 basis elements and 18 pairs
    8 basis elements and 17 pairs
    8 basis elements and 16 pairs
    8 basis elements and 15 pairs
    8 basis elements and 14 pairs
    9 basis elements and 21 pairs
    9 basis elements and 20 pairs
    10 basis elements and 28 pairs
    10 basis elements and 27 pairs
    10 basis elements and 26 pairs
    10 basis elements and 25 pairs
    4 basis elements and 6 pairs
    4 basis elements and 5 pairs
    4 basis elements and 4 pairs
    5 basis elements and 7 pairs
    5 basis elements and 6 pairs
    4 basis elements and 6 pairs
    4 basis elements and 5 pairs
    4 basis elements and 4 pairs
    5 basis elements and 7 pairs
    5 basis elements and 6 pairs
    4 basis elements and 6 pairs
    4 basis elements and 5 pairs
    5 basis elements and 8 pairs
    6 basis elements and 12 pairs
    7 basis elements and 17 pairs
    8 basis elements and 23 pairs
    9 basis elements and 30 pairs
    9 basis elements and 29 pairs
    9 basis elements and 28 pairs
    9 basis elements and 27 pairs
    4 basis elements and 6 pairs
    4 basis elements and 5 pairs
    5 basis elements and 8 pairs
    6 basis elements and 12 pairs
    7 basis elements and 17 pairs
    true
    |}]
;;

(* ------------------------------------------------------------------------- *)
(* And show we can always invent such a transformation to zero a y:          *)
(* ------------------------------------------------------------------------- *)

let%expect_test "eg: And show we can always invent such a transformation to zero a y:" =
  print_fol_formula
    (real_qelim
     {%fol|forall x y. exists s c. s^2 + c^2 = 1 /\ s * x + c * y = 0|});
  [%expect {| <<true>> |}]
;;


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

let%expect_test _ =
  print_bool
    (forall (grobner_decide ** invariant_under_scaling) coordinations);
  print_pair (print_list (print_pair print_quoted print_fol_formula))
             (print_list (print_pair print_quoted print_fol_formula))
    (partition (grobner_decide ** invariant_under_shearing) coordinations);
  [%expect {|
    3 basis elements and 3 pairs
    3 basis elements and 2 pairs
    3 basis elements and 3 pairs
    4 basis elements and 5 pairs
    5 basis elements and 8 pairs
    5 basis elements and 7 pairs
    5 basis elements and 6 pairs
    6 basis elements and 10 pairs
    7 basis elements and 15 pairs
    7 basis elements and 14 pairs
    7 basis elements and 13 pairs
    7 basis elements and 12 pairs
    7 basis elements and 11 pairs
    7 basis elements and 10 pairs
    7 basis elements and 9 pairs
    7 basis elements and 8 pairs
    8 basis elements and 14 pairs
    3 basis elements and 3 pairs
    3 basis elements and 2 pairs
    3 basis elements and 3 pairs
    4 basis elements and 5 pairs
    5 basis elements and 8 pairs
    5 basis elements and 7 pairs
    5 basis elements and 6 pairs
    6 basis elements and 10 pairs
    7 basis elements and 15 pairs
    7 basis elements and 14 pairs
    7 basis elements and 13 pairs
    7 basis elements and 12 pairs
    7 basis elements and 11 pairs
    7 basis elements and 10 pairs
    7 basis elements and 9 pairs
    7 basis elements and 8 pairs
    8 basis elements and 14 pairs
    3 basis elements and 3 pairs
    3 basis elements and 2 pairs
    3 basis elements and 3 pairs
    4 basis elements and 5 pairs
    5 basis elements and 8 pairs
    5 basis elements and 7 pairs
    5 basis elements and 6 pairs
    6 basis elements and 10 pairs
    7 basis elements and 15 pairs
    7 basis elements and 14 pairs
    7 basis elements and 13 pairs
    7 basis elements and 12 pairs
    7 basis elements and 11 pairs
    7 basis elements and 10 pairs
    7 basis elements and 9 pairs
    7 basis elements and 8 pairs
    8 basis elements and 14 pairs
    3 basis elements and 3 pairs
    3 basis elements and 2 pairs
    3 basis elements and 3 pairs
    4 basis elements and 5 pairs
    5 basis elements and 8 pairs
    5 basis elements and 7 pairs
    5 basis elements and 6 pairs
    6 basis elements and 10 pairs
    7 basis elements and 15 pairs
    7 basis elements and 14 pairs
    7 basis elements and 13 pairs
    7 basis elements and 12 pairs
    7 basis elements and 11 pairs
    7 basis elements and 10 pairs
    7 basis elements and 9 pairs
    7 basis elements and 8 pairs
    8 basis elements and 14 pairs
    4 basis elements and 6 pairs
    4 basis elements and 5 pairs
    4 basis elements and 4 pairs
    4 basis elements and 6 pairs
    4 basis elements and 5 pairs
    4 basis elements and 4 pairs
    5 basis elements and 7 pairs
    5 basis elements and 6 pairs
    4 basis elements and 6 pairs
    4 basis elements and 5 pairs
    5 basis elements and 8 pairs
    6 basis elements and 12 pairs
    7 basis elements and 17 pairs
    7 basis elements and 16 pairs
    8 basis elements and 22 pairs
    8 basis elements and 21 pairs
    8 basis elements and 20 pairs
    9 basis elements and 27 pairs
    4 basis elements and 6 pairs
    4 basis elements and 5 pairs
    5 basis elements and 8 pairs
    6 basis elements and 12 pairs
    7 basis elements and 17 pairs
    8 basis elements and 23 pairs
    9 basis elements and 30 pairs
    9 basis elements and 29 pairs
    9 basis elements and 28 pairs
    10 basis elements and 36 pairs
    10 basis elements and 35 pairs
    10 basis elements and 34 pairs
    10 basis elements and 33 pairs
    10 basis elements and 32 pairs
    11 basis elements and 41 pairs
    11 basis elements and 40 pairs
    11 basis elements and 39 pairs
    11 basis elements and 38 pairs
    11 basis elements and 37 pairs
    11 basis elements and 36 pairs
    12 basis elements and 46 pairs
    4 basis elements and 6 pairs
    4 basis elements and 5 pairs
    4 basis elements and 4 pairs
    4 basis elements and 6 pairs
    4 basis elements and 5 pairs
    4 basis elements and 4 pairs
    5 basis elements and 7 pairs
    5 basis elements and 6 pairs
    4 basis elements and 6 pairs
    4 basis elements and 5 pairs
    5 basis elements and 8 pairs
    6 basis elements and 12 pairs
    7 basis elements and 17 pairs
    7 basis elements and 16 pairs
    7 basis elements and 15 pairs
    7 basis elements and 14 pairs
    7 basis elements and 13 pairs
    8 basis elements and 19 pairs
    9 basis elements and 26 pairs
    9 basis elements and 25 pairs
    9 basis elements and 24 pairs
    9 basis elements and 23 pairs
    9 basis elements and 22 pairs
    9 basis elements and 21 pairs
    9 basis elements and 20 pairs
    9 basis elements and 19 pairs
    9 basis elements and 18 pairs
    9 basis elements and 17 pairs
    10 basis elements and 25 pairs
    10 basis elements and 24 pairs
    10 basis elements and 23 pairs
    10 basis elements and 22 pairs
    10 basis elements and 21 pairs
    10 basis elements and 20 pairs
    10 basis elements and 19 pairs
    11 basis elements and 28 pairs
    4 basis elements and 6 pairs
    4 basis elements and 5 pairs
    5 basis elements and 8 pairs
    6 basis elements and 12 pairs
    7 basis elements and 17 pairs
    8 basis elements and 23 pairs
    8 basis elements and 22 pairs
    8 basis elements and 21 pairs
    8 basis elements and 20 pairs
    9 basis elements and 27 pairs
    10 basis elements and 35 pairs
    10 basis elements and 34 pairs
    10 basis elements and 33 pairs
    10 basis elements and 32 pairs
    11 basis elements and 41 pairs
    11 basis elements and 40 pairs
    11 basis elements and 39 pairs
    12 basis elements and 49 pairs
    12 basis elements and 48 pairs
    12 basis elements and 47 pairs
    13 basis elements and 58 pairs
    14 basis elements and 70 pairs
    14 basis elements and 69 pairs
    14 basis elements and 68 pairs
    14 basis elements and 67 pairs
    14 basis elements and 66 pairs
    14 basis elements and 65 pairs
    14 basis elements and 64 pairs
    14 basis elements and 63 pairs
    14 basis elements and 62 pairs
    14 basis elements and 61 pairs
    14 basis elements and 60 pairs
    14 basis elements and 59 pairs
    14 basis elements and 58 pairs
    14 basis elements and 57 pairs
    15 basis elements and 70 pairs
    15 basis elements and 69 pairs
    15 basis elements and 68 pairs
    15 basis elements and 67 pairs
    15 basis elements and 66 pairs
    15 basis elements and 65 pairs
    15 basis elements and 64 pairs
    15 basis elements and 63 pairs
    15 basis elements and 62 pairs
    16 basis elements and 76 pairs
    16 basis elements and 75 pairs
    16 basis elements and 74 pairs
    16 basis elements and 73 pairs
    16 basis elements and 72 pairs
    16 basis elements and 71 pairs
    16 basis elements and 70 pairs
    16 basis elements and 69 pairs
    16 basis elements and 68 pairs
    16 basis elements and 67 pairs
    17 basis elements and 82 pairs
    17 basis elements and 81 pairs
    17 basis elements and 80 pairs
    17 basis elements and 79 pairs
    17 basis elements and 78 pairs
    17 basis elements and 77 pairs
    17 basis elements and 76 pairs
    17 basis elements and 75 pairs
    17 basis elements and 74 pairs
    17 basis elements and 73 pairs
    17 basis elements and 72 pairs
    18 basis elements and 88 pairs
    18 basis elements and 87 pairs
    18 basis elements and 86 pairs
    18 basis elements and 85 pairs
    18 basis elements and 84 pairs
    18 basis elements and 83 pairs
    18 basis elements and 82 pairs
    18 basis elements and 81 pairs
    18 basis elements and 80 pairs
    18 basis elements and 79 pairs
    18 basis elements and 78 pairs
    18 basis elements and 77 pairs
    19 basis elements and 94 pairs
    4 basis elements and 6 pairs
    4 basis elements and 5 pairs
    4 basis elements and 4 pairs
    4 basis elements and 6 pairs
    4 basis elements and 5 pairs
    4 basis elements and 4 pairs
    5 basis elements and 7 pairs
    5 basis elements and 6 pairs
    4 basis elements and 6 pairs
    4 basis elements and 5 pairs
    5 basis elements and 8 pairs
    6 basis elements and 12 pairs
    6 basis elements and 11 pairs
    7 basis elements and 16 pairs
    7 basis elements and 15 pairs
    7 basis elements and 14 pairs
    7 basis elements and 13 pairs
    7 basis elements and 12 pairs
    4 basis elements and 6 pairs
    4 basis elements and 5 pairs
    5 basis elements and 8 pairs
    6 basis elements and 12 pairs
    7 basis elements and 17 pairs
    8 basis elements and 23 pairs
    8 basis elements and 22 pairs
    8 basis elements and 21 pairs
    8 basis elements and 20 pairs
    8 basis elements and 19 pairs
    9 basis elements and 26 pairs
    9 basis elements and 25 pairs
    9 basis elements and 24 pairs
    9 basis elements and 23 pairs
    9 basis elements and 22 pairs
    9 basis elements and 21 pairs
    9 basis elements and 20 pairs
    9 basis elements and 19 pairs
    9 basis elements and 18 pairs
    9 basis elements and 17 pairs
    9 basis elements and 16 pairs
    true3 basis elements and 3 pairs
    3 basis elements and 2 pairs
    4 basis elements and 4 pairs
    3 basis elements and 3 pairs
    4 basis elements and 5 pairs
    5 basis elements and 8 pairs
    5 basis elements and 7 pairs
    5 basis elements and 6 pairs
    5 basis elements and 5 pairs
    3 basis elements and 3 pairs
    3 basis elements and 2 pairs
    3 basis elements and 3 pairs
    3 basis elements and 2 pairs
    4 basis elements and 4 pairs
    3 basis elements and 3 pairs
    3 basis elements and 2 pairs
    3 basis elements and 3 pairs
    3 basis elements and 2 pairs
    4 basis elements and 4 pairs
    3 basis elements and 3 pairs
    3 basis elements and 2 pairs
    4 basis elements and 4 pairs
    3 basis elements and 3 pairs
    4 basis elements and 5 pairs
    5 basis elements and 8 pairs
    5 basis elements and 7 pairs
    5 basis elements and 6 pairs
    5 basis elements and 5 pairs
    2 basis elements and 1 pairs
    3 basis elements and 2 pairs
    3 basis elements and 1 pairs
    3 basis elements and 0 pairs
    2 basis elements and 1 pairs
    3 basis elements and 2 pairs
    3 basis elements and 1 pairs
    3 basis elements and 0 pairs
    2 basis elements and 1 pairs
    2 basis elements and 1 pairs
    2 basis elements and 1 pairs
    2 basis elements and 1 pairs
    ([("collinear", <<(1_x - 2_x) * (2_y - 3_y) = (1_y - 2_y) * (2_x - 3_x)>>); ("parallel",
    <<(1_x - 2_x) * (3_y - 4_y) = (1_y - 2_y) * (3_x - 4_x)>>); ("is_midpoint",
    <<2 * 1_x = 2_x + 3_x /\ 2 * 1_y = 2_y + 3_y>>); ("is_intersection",
    <<(1_x - 2_x) * (2_y - 3_y) = (1_y - 2_y) * (2_x - 3_x) /\ (1_x - 4_x) *
      (4_y - 5_y) = (1_y - 4_y) * (4_x - 5_x)>>); ("=", <<1_x = 2_x /\ 1_y = 2_y>>)], [("perpendicular",
    <<(1_x - 2_x) * (3_x - 4_x) + (1_y - 2_y) * (3_y - 4_y) = 0>>); ("lengths_eq",
    <<(1_x - 2_x)^2 + (1_y - 2_y)^2 = (3_x - 4_x)^2 + (3_y - 4_y)^2>>)])
    |}]
;;


(* ------------------------------------------------------------------------- *)
(* One from "Algorithms for Computer Algebra"                                *)
(* ------------------------------------------------------------------------- *)


(* ------------------------------------------------------------------------- *)
let%expect_test "eg: One from 'Algorithms for Computer Algebra'" =
  print_bool
    ((grobner_decide ** originate)
     {%fol|is_midpoint(m,a,c) /\ perpendicular(a,c,m,b)
       ==> lengths_eq(a,b,b,c)|});
  (* ------------------------------------------------------------------------- *)
  (* Parallelogram theorem (Chou's expository example at the start).           *)
  (* ------------------------------------------------------------------------- *)
  print_bool
    ((grobner_decide ** originate)
     {%fol|parallel(a,b,d,c) /\ parallel(a,d,b,c) /\
       is_intersection(e,a,c,b,d)
       ==> lengths_eq(a,e,e,c)|});
  print_bool
    ((grobner_decide ** originate)
     {%fol|parallel(a,b,d,c) /\ parallel(a,d,b,c) /\
       is_intersection(e,a,c,b,d) /\ ~collinear(a,b,c)
       ==> lengths_eq(a,e,e,c)|});
  [%expect {|
    4 basis elements and 6 pairs
    4 basis elements and 5 pairs
    5 basis elements and 8 pairs
    6 basis elements and 12 pairs
    7 basis elements and 17 pairs
    8 basis elements and 23 pairs
    8 basis elements and 22 pairs
    8 basis elements and 21 pairs
    8 basis elements and 20 pairs
    8 basis elements and 19 pairs
    8 basis elements and 18 pairs
    8 basis elements and 17 pairs
    8 basis elements and 16 pairs
    8 basis elements and 15 pairs
    8 basis elements and 14 pairs
    8 basis elements and 13 pairs
    8 basis elements and 12 pairs
    8 basis elements and 11 pairs
    8 basis elements and 10 pairs
    8 basis elements and 9 pairs
    8 basis elements and 8 pairs
    true5 basis elements and 10 pairs
    6 basis elements and 14 pairs
    7 basis elements and 19 pairs
    7 basis elements and 18 pairs
    8 basis elements and 24 pairs
    8 basis elements and 23 pairs
    9 basis elements and 30 pairs
    10 basis elements and 38 pairs
    10 basis elements and 37 pairs
    11 basis elements and 46 pairs
    12 basis elements and 56 pairs
    12 basis elements and 55 pairs
    12 basis elements and 54 pairs
    12 basis elements and 53 pairs
    12 basis elements and 52 pairs
    13 basis elements and 63 pairs
    13 basis elements and 62 pairs
    13 basis elements and 61 pairs
    13 basis elements and 60 pairs
    13 basis elements and 59 pairs
    13 basis elements and 58 pairs
    13 basis elements and 57 pairs
    13 basis elements and 56 pairs
    13 basis elements and 55 pairs
    13 basis elements and 54 pairs
    13 basis elements and 53 pairs
    13 basis elements and 52 pairs
    13 basis elements and 51 pairs
    13 basis elements and 50 pairs
    13 basis elements and 49 pairs
    13 basis elements and 48 pairs
    13 basis elements and 47 pairs
    13 basis elements and 46 pairs
    13 basis elements and 45 pairs
    13 basis elements and 44 pairs
    13 basis elements and 43 pairs
    13 basis elements and 42 pairs
    13 basis elements and 41 pairs
    13 basis elements and 40 pairs
    13 basis elements and 39 pairs
    13 basis elements and 38 pairs
    13 basis elements and 37 pairs
    13 basis elements and 36 pairs
    13 basis elements and 35 pairs
    13 basis elements and 34 pairs
    13 basis elements and 33 pairs
    13 basis elements and 32 pairs
    13 basis elements and 31 pairs
    13 basis elements and 30 pairs
    13 basis elements and 29 pairs
    13 basis elements and 28 pairs
    13 basis elements and 27 pairs
    13 basis elements and 26 pairs
    13 basis elements and 25 pairs
    13 basis elements and 24 pairs
    13 basis elements and 23 pairs
    13 basis elements and 22 pairs
    13 basis elements and 21 pairs
    13 basis elements and 20 pairs
    13 basis elements and 19 pairs
    13 basis elements and 18 pairs
    13 basis elements and 17 pairs
    13 basis elements and 16 pairs
    13 basis elements and 15 pairs
    13 basis elements and 14 pairs
    13 basis elements and 13 pairs
    13 basis elements and 12 pairs
    13 basis elements and 11 pairs
    13 basis elements and 10 pairs
    14 basis elements and 22 pairs
    15 basis elements and 35 pairs
    15 basis elements and 34 pairs
    15 basis elements and 33 pairs
    15 basis elements and 32 pairs
    15 basis elements and 31 pairs
    15 basis elements and 30 pairs
    15 basis elements and 29 pairs
    15 basis elements and 28 pairs
    15 basis elements and 27 pairs
    15 basis elements and 26 pairs
    15 basis elements and 25 pairs
    15 basis elements and 24 pairs
    15 basis elements and 23 pairs
    15 basis elements and 22 pairs
    15 basis elements and 21 pairs
    15 basis elements and 20 pairs
    15 basis elements and 19 pairs
    15 basis elements and 18 pairs
    15 basis elements and 17 pairs
    15 basis elements and 16 pairs
    15 basis elements and 15 pairs
    15 basis elements and 14 pairs
    15 basis elements and 13 pairs
    15 basis elements and 12 pairs
    15 basis elements and 11 pairs
    15 basis elements and 10 pairs
    15 basis elements and 9 pairs
    15 basis elements and 8 pairs
    15 basis elements and 7 pairs
    15 basis elements and 6 pairs
    15 basis elements and 5 pairs
    15 basis elements and 4 pairs
    15 basis elements and 3 pairs
    15 basis elements and 2 pairs
    15 basis elements and 1 pairs
    15 basis elements and 0 pairs
    false6 basis elements and 15 pairs
    7 basis elements and 20 pairs
    8 basis elements and 26 pairs
    8 basis elements and 25 pairs
    9 basis elements and 32 pairs
    10 basis elements and 40 pairs
    10 basis elements and 39 pairs
    11 basis elements and 48 pairs
    12 basis elements and 58 pairs
    13 basis elements and 69 pairs
    13 basis elements and 68 pairs
    14 basis elements and 80 pairs
    15 basis elements and 93 pairs
    16 basis elements and 107 pairs
    17 basis elements and 122 pairs
    18 basis elements and 138 pairs
    18 basis elements and 137 pairs
    18 basis elements and 136 pairs
    18 basis elements and 135 pairs
    18 basis elements and 134 pairs
    19 basis elements and 151 pairs
    20 basis elements and 169 pairs
    20 basis elements and 168 pairs
    20 basis elements and 167 pairs
    20 basis elements and 166 pairs
    20 basis elements and 165 pairs
    20 basis elements and 164 pairs
    20 basis elements and 163 pairs
    20 basis elements and 162 pairs
    20 basis elements and 161 pairs
    20 basis elements and 160 pairs
    21 basis elements and 179 pairs
    21 basis elements and 178 pairs
    21 basis elements and 177 pairs
    22 basis elements and 197 pairs
    22 basis elements and 196 pairs
    22 basis elements and 195 pairs
    22 basis elements and 194 pairs
    22 basis elements and 193 pairs
    22 basis elements and 192 pairs
    22 basis elements and 191 pairs
    22 basis elements and 190 pairs
    22 basis elements and 189 pairs
    22 basis elements and 188 pairs
    22 basis elements and 187 pairs
    22 basis elements and 186 pairs
    22 basis elements and 185 pairs
    22 basis elements and 184 pairs
    22 basis elements and 183 pairs
    22 basis elements and 182 pairs
    22 basis elements and 181 pairs
    22 basis elements and 180 pairs
    22 basis elements and 179 pairs
    22 basis elements and 178 pairs
    22 basis elements and 177 pairs
    22 basis elements and 176 pairs
    22 basis elements and 175 pairs
    22 basis elements and 174 pairs
    23 basis elements and 195 pairs
    23 basis elements and 194 pairs
    23 basis elements and 193 pairs
    24 basis elements and 215 pairs
    24 basis elements and 214 pairs
    24 basis elements and 213 pairs
    24 basis elements and 212 pairs
    25 basis elements and 235 pairs
    25 basis elements and 234 pairs
    25 basis elements and 233 pairs
    25 basis elements and 232 pairs
    25 basis elements and 231 pairs
    25 basis elements and 230 pairs
    25 basis elements and 229 pairs
    25 basis elements and 228 pairs
    25 basis elements and 227 pairs
    25 basis elements and 226 pairs
    25 basis elements and 225 pairs
    25 basis elements and 224 pairs
    25 basis elements and 223 pairs
    25 basis elements and 222 pairs
    25 basis elements and 221 pairs
    25 basis elements and 220 pairs
    25 basis elements and 219 pairs
    25 basis elements and 218 pairs
    25 basis elements and 217 pairs
    25 basis elements and 216 pairs
    25 basis elements and 215 pairs
    25 basis elements and 214 pairs
    25 basis elements and 213 pairs
    25 basis elements and 212 pairs
    25 basis elements and 211 pairs
    26 basis elements and 235 pairs
    26 basis elements and 234 pairs
    26 basis elements and 233 pairs
    26 basis elements and 232 pairs
    26 basis elements and 231 pairs
    26 basis elements and 230 pairs
    26 basis elements and 229 pairs
    26 basis elements and 228 pairs
    26 basis elements and 227 pairs
    26 basis elements and 226 pairs
    26 basis elements and 225 pairs
    26 basis elements and 224 pairs
    26 basis elements and 223 pairs
    26 basis elements and 222 pairs
    true
    |}]
;;

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

let%expect_test "eg: Simson's theorem" =
  let simson =
   {%fol|lengths_eq(o,a,o,b) /\
     lengths_eq(o,a,o,c) /\
     lengths_eq(o,a,o,d) /\
     collinear(e,b,c) /\
     collinear(f,a,c) /\
     collinear(g,a,b) /\
     perpendicular(b,c,d,e) /\
     perpendicular(a,c,d,f) /\
     perpendicular(a,b,d,g)
     ==> collinear(e,f,g)|} in
  print_fol_formula
    (simson);
  let vars =
   ["g_y"; "g_x"; "f_y"; "f_x"; "e_y"; "e_x"; "d_y"; "d_x"; "c_y"; "c_x";
    "b_y"; "b_x"; "o_x"]
  and zeros = ["a_x"; "a_y"; "o_y"] in
  print_list print_quoted
    (vars);
  print_list print_fol_formula
    (wu simson vars zeros);
  (* ------------------------------------------------------------------------- *)
  (* Try without special coordinates.                                          *)
  (* ------------------------------------------------------------------------- *)
  print_list print_fol_formula
    (wu simson (vars @ zeros) []);
  (* ------------------------------------------------------------------------- *)
  (* Pappus (Chou's figure 6).                                                 *)
  (* ------------------------------------------------------------------------- *)
  let pappus =
   {%fol|collinear(a1,b2,d) /\
     collinear(a2,b1,d) /\
     collinear(a2,b3,e) /\
     collinear(a3,b2,e) /\
     collinear(a1,b3,f) /\
     collinear(a3,b1,f)
     ==> collinear(d,e,f)|} in
  print_fol_formula
    (pappus);
  let vars = ["f_y"; "f_x"; "e_y"; "e_x"; "d_y"; "d_x";
              "b3_y"; "b2_y"; "b1_y"; "a3_x"; "a2_x"; "a1_x"]
  and zeros = ["a1_y"; "a2_y"; "a3_y"; "b1_x"; "b2_x"; "b3_x"] in
  print_list print_quoted
    (vars);
  print_list print_fol_formula
    (wu pappus vars zeros);
  (* ------------------------------------------------------------------------- *)
  (* The Butterfly (figure 9).                                                 *)
  (* ------------------------------------------------------------------------- *)

  (****
  let butterfly =
   {%fol|lengths_eq(b,o,a,o) /\ lengths_eq(c,o,a,o) /\ lengths_eq(d,o,a,o) /\
     collinear(a,e,c) /\ collinear(d,e,b) /\
     perpendicular(e,f,o,e) /\
     collinear(a,f,d) /\ collinear(f,e,g) /\ collinear(b,c,g)
     ==> is_midpoint(e,f,g)|};;

  let vars = ["g_y"; "g_x"; "f_y"; "f_x"; "e_y"; "e_x"; "d_y"; "c_y";
              "b_y"; "d_x"; "c_x"; "b_x"; "a_x"]
  and zeros = ["a_y"; "o_x"; "o_y"];;

   **** This one is costly (too big for laptop, but doable in about 300M)
   **** However, it gives exactly the same degenerate conditions as Chou

  wu butterfly vars zeros;;

   ****
   ****)
  [%expect {|
    <<lengths_eq(o,a,o,b) /\
      lengths_eq(o,a,o,c) /\
      lengths_eq(o,a,o,d) /\
      collinear(e,b,c) /\
      collinear(f,a,c) /\
      collinear(g,a,b) /\
      perpendicular(b,c,d,e) /\ perpendicular(a,c,d,f) /\ perpendicular(a,b,d,g) ==>
      collinear(e,f,g)>>["g_y"; "g_x"; "f_y"; "f_x"; "e_y"; "e_x"; "d_y"; "d_x"; "c_y"; "c_x"; "b_y"; "b_x"; "o_x"][
    <<~(((0 + b_x * (0 + b_x * 1)) + b_y * (0 + b_y * 1)) + c_x *
        ((0 + b_x * -2) + c_x * 1)) +
       c_y * ((0 + b_y * -2) + c_y * 1) = 0>>; <<~(0 + b_x * (0 + b_x * 1)) +
                                                  b_y * (0 + b_y * 1) = 0>>;
    <<~(0 + b_x * -1) + c_x * 1 = 0>>; <<~(0 + c_x * (0 + c_x * 1)) + c_y *
                                          (0 + c_y * 1) = 0>>; <<~0 + b_x * 1 = 0>>;
    <<~0 + c_x * 1 = 0>>; <<~-1 = 0>>][<<~(((0 + a_y * (0 + a_y * 1)) + a_x *
                                            (0 + a_x * 1)) +
                                           b_x * ((0 + a_x * -2) + b_x * 1)) +
                                          b_y * ((0 + a_y * -2) + b_y * 1) = 0>>;
    <<~(((0 + a_y * (0 + a_y * 1)) + a_x * (0 + a_x * 1)) + c_x *
        ((0 + a_x * -2) + c_x * 1)) +
       c_y * ((0 + a_y * -2) + c_y * 1) = 0>>; <<~(((0 + b_x * (0 + b_x * 1)) +
                                                    b_y * (0 + b_y * 1)) +
                                                   c_x *
                                                   ((0 + b_x * -2) + c_x * 1)) +
                                                  c_y *
                                                  ((0 + b_y * -2) + c_y * 1) = 0>>;
    <<~(0 + a_x * -1) + b_x * 1 = 0>>; <<~(0 + a_x * -1) + c_x * 1 = 0>>;
    <<~(0 + b_x * -1) + c_x * 1 = 0>>; <<~-1 = 0>>]<<collinear(a1,b2,d) /\
                                                     collinear(a2,b1,d) /\
                                                     collinear(a2,b3,e) /\
                                                     collinear(a3,b2,e) /\
                                                     collinear(a1,b3,f) /\
                                                     collinear(a3,b1,f) ==>
                                                     collinear(d,e,f)>>["f_y"; "f_x"; "e_y"; "e_x"; "d_y"; "d_x"; "b3_y"; "b2_y"; "b1_y"; "a3_x"; "a2_x"; "a1_x"][
    <<~(0 + b1_y * (0 + a1_x * 1)) + b2_y * (0 + a2_x * -1) = 0>>; <<~(0 + b1_y *
                                                                       (0 +
                                                                        a1_x * 1)) +
                                                                      b3_y *
                                                                      (0 + a3_x *
                                                                       -1) =
                                                                      0>>;
    <<~(0 + b2_y * (0 + a2_x * 1)) + b3_y * (0 + a3_x * -1) = 0>>; <<~0 + a1_x *
                                                                      -1 = 0>>;
    <<~0 + a2_x * -1 = 0>>]
    |}]
;;


(*** Other examples removed from text

(* ------------------------------------------------------------------------- *)
(* Centroid (Chou, example 142).                                             *)
(* ------------------------------------------------------------------------- *)

(grobner_decide ** originate)
 {%fol|is_midpoint(d,b,c) /\ is_midpoint(e,a,c) /\
   is_midpoint(f,a,b) /\ is_intersection(m,b,e,a,d)
   ==> collinear(c,f,m)|};;

****)
