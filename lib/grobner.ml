open Lib
open Formulas
open Prop
open Fol
open Complex
open Skolem
open Order
open Cooper

(* ========================================================================= *)
(* Grobner basis algorithm.                                                  *)
(*                                                                           *)
(* Copyright (c) 2003-2007, John Harrison. (See "LICENSE.txt" for details.)  *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Operations on monomials.                                                  *)
(* ------------------------------------------------------------------------- *)

let mmul (c1,m1) (c2,m2) = (c1*/c2,map2 (+) m1 m2);;

let mdiv =
  let index_sub n1 n2 = if n1 < n2 then failwith "mdiv" else n1-n2 in
  fun (c1,m1) (c2,m2) -> (c1//c2,map2 index_sub m1 m2);;

let mlcm (c1,m1) (c2,m2) = (Int 1,map2 max m1 m2);;

(* ------------------------------------------------------------------------- *)
(* Monomial ordering.                                                        *)
(* ------------------------------------------------------------------------- *)

let morder_lt m1 m2 =
  let n1 = itlist (+) m1 0 and n2 = itlist (+) m2 0 in
  n1 < n2 || n1 = n2 && lexord(>) m1 m2;;

(* ------------------------------------------------------------------------- *)
(* Arithmetic on canonical multivariate polynomials.                         *)
(* ------------------------------------------------------------------------- *)

let mpoly_mmul cm pol = map (mmul cm) pol;;

let mpoly_neg = map (fun (c,m) -> (minus_num c,m));;

let mpoly_const vars c =
  if c =/ Int 0 then [] else [c,map (fun k -> 0) vars];;

let mpoly_var vars x =
  [Int 1,map (fun y -> if y = x then 1 else 0) vars];;

let rec mpoly_add l1 l2 =
  match (l1,l2) with
    ([],l2) -> l2
  | (l1,[]) -> l1
  | ((c1,m1)::o1,(c2,m2)::o2) ->
        if m1 = m2 then
          let c = c1+/c2 and rest = mpoly_add o1 o2 in
          if c =/ Int 0 then rest else (c,m1)::rest
        else if morder_lt m2 m1 then (c1,m1)::(mpoly_add o1 l2)
        else (c2,m2)::(mpoly_add l1 o2);;

let mpoly_sub l1 l2 = mpoly_add l1 (mpoly_neg l2);;

let rec mpoly_mul l1 l2 =
  match l1 with
    [] -> []
  | (h1::t1) -> mpoly_add (mpoly_mmul h1 l2) (mpoly_mul t1 l2);;

let mpoly_pow vars l n =
  funpow n (mpoly_mul l) (mpoly_const vars (Int 1));;

let mpoly_inv p =
  match p with 
    [(c,m)] when forall (fun i -> i = 0) m -> [(Int 1 // c),m]
  | _ -> failwith "mpoly_inv: non-constant polynomial";;

let mpoly_div p q = mpoly_mul p (mpoly_inv q);;

(* ------------------------------------------------------------------------- *)
(* Convert formula into canonical form.                                      *)
(* ------------------------------------------------------------------------- *)

let rec mpolynate vars tm =
  match tm with
    Var x -> mpoly_var vars x
  | Fn("-",[t]) -> mpoly_neg (mpolynate vars t)
  | Fn("+",[s;t]) -> mpoly_add (mpolynate vars s) (mpolynate vars t)
  | Fn("-",[s;t]) -> mpoly_sub (mpolynate vars s) (mpolynate vars t)
  | Fn("*",[s;t]) -> mpoly_mul (mpolynate vars s) (mpolynate vars t)
  | Fn("/",[s;t]) -> mpoly_div (mpolynate vars s) (mpolynate vars t)
  | Fn("^",[t;Fn(n,[])]) ->
                mpoly_pow vars (mpolynate vars t) (int_of_string n)
  | _ -> mpoly_const vars (dest_numeral tm);;

let mpolyatom vars fm =
  match fm with
    Atom(R("=",[s;t])) -> mpolynate vars (Fn("-",[s;t]))
  | _ -> failwith "mpolyatom: not an equation";;

(* ------------------------------------------------------------------------- *)
(* Reduce monomial cm by polynomial pol, returning replacement for cm.       *)
(* ------------------------------------------------------------------------- *)

let reduce1 cm pol =
  match pol with
    [] -> failwith "reduce1"
  | hm::cms -> let c,m = mdiv cm hm in mpoly_mmul (minus_num c,m) cms;;

(* ------------------------------------------------------------------------- *)
(* Try this for all polynomials in a basis.                                  *)
(* ------------------------------------------------------------------------- *)

let reduceb cm pols = tryfind (reduce1 cm) pols;;

(* ------------------------------------------------------------------------- *)
(* Reduction of a polynomial (always picking largest monomial possible).     *)
(* ------------------------------------------------------------------------- *)

let rec reduce pols pol =
  match pol with
    [] -> []
  | cm::ptl -> try reduce pols (mpoly_add (reduceb cm pols) ptl)
               with Failure _ -> cm::(reduce pols ptl);;

(* ------------------------------------------------------------------------- *)
(* Compute S-polynomial of two polynomials.                                  *)
(* ------------------------------------------------------------------------- *)

let spoly pol1 pol2 =
  match (pol1,pol2) with
    ([],p) -> []
  | (p,[]) -> []
  | (m1::ptl1,m2::ptl2) ->
        let m = mlcm m1 m2 in
        mpoly_sub (mpoly_mmul (mdiv m m1) ptl1)
                  (mpoly_mmul (mdiv m m2) ptl2);;

(* ------------------------------------------------------------------------- *)
(* Grobner basis algorithm.                                                  *)
(* ------------------------------------------------------------------------- *)

let rec grobner basis pairs =
  print_string(string_of_int(length basis)^" basis elements and "^
               string_of_int(length pairs)^" pairs");
  print_newline();
  match pairs with
    [] -> basis
  | (p1,p2)::opairs ->
        let sp = reduce basis (spoly p1 p2) in
        if sp = [] then grobner basis opairs
        else if forall (forall ((=) 0) ** snd) sp then [sp] else
        let newcps = map (fun p -> p,sp) basis in
        grobner (sp::basis) (opairs @ newcps);;

(* ------------------------------------------------------------------------- *)
(* Overall function.                                                         *)
(* ------------------------------------------------------------------------- *)

let groebner basis = grobner basis (distinctpairs basis);;

(* ------------------------------------------------------------------------- *)
(* Use the Rabinowitsch trick to eliminate inequations.                      *)
(* That is, replace p =/= 0 by exists v. 1 - v * p = 0                       *)
(* ------------------------------------------------------------------------- *)

let rabinowitsch vars v p =
   mpoly_sub (mpoly_const vars (Int 1))
             (mpoly_mul (mpoly_var vars v) p);;

(* ------------------------------------------------------------------------- *)
(* Universal complex number decision procedure based on Grobner bases.       *)
(* ------------------------------------------------------------------------- *)

let grobner_trivial fms =
  let vars0 = itlist (union ** fv) fms []
  and eqs,neqs = partition positive fms in
  let rvs = map (fun n -> variant ("_"^string_of_int n) vars0)
                (1--length neqs) in
  let vars = vars0 @ rvs in
  let poleqs = map (mpolyatom vars) eqs
  and polneqs = map (mpolyatom vars ** negate) neqs in
  let pols = poleqs @ map2 (rabinowitsch vars) rvs polneqs in
  reduce (groebner pols) (mpoly_const vars (Int 1)) = [];;

let grobner_decide fm =
  let fm1 = specialize(prenex(nnf(simplify fm))) in
  forall grobner_trivial (simpdnf(nnf(Not fm1)));;

let%expect_test "eg: Examples" =
  print_bool
    (grobner_decide
      {%fol|a^2 = 2 /\ x^2 + a*x + 1 = 0 ==> x^4 + 1 = 0|});
  print_bool
    (grobner_decide
      {%fol|a^2 = 2 /\ x^2 + a*x + 1 = 0 ==> x^4 + 2 = 0|});
  print_bool
    (grobner_decide
      {%fol|(a * x^2 + b * x + c = 0) /\
       (a * y^2 + b * y + c = 0) /\
       ~(x = y)
       ==> (a * x * y = c) /\ (a * (x + y) + b = 0)|});
  (* ------------------------------------------------------------------------- *)
  (* Compare with earlier procedure.                                           *)
  (* ------------------------------------------------------------------------- *)
  print_pair print_fol_formula print_bool
    (let fm =
      {%fol|(a * x^2 + b * x + c = 0) /\
        (a * y^2 + b * y + c = 0) /\
        ~(x = y)
        ==> (a * x * y = c) /\ (a * (x + y) + b = 0)|} in
    complex_qelim (generalize fm),grobner_decide fm);
  (* ------------------------------------------------------------------------- *)
  (* More tests.                                                               *)
  (* ------------------------------------------------------------------------- *)
  print_bool
    (grobner_decide  {%fol|a^2 = 2 /\ x^2 + a*x + 1 = 0 ==> x^4 + 1 = 0|});
  print_bool
    (grobner_decide  {%fol|a^2 = 2 /\ x^2 + a*x + 1 = 0 ==> x^4 + 2 = 0|});
  print_bool
    (grobner_decide {%fol|(a * x^2 + b * x + c = 0) /\
          (a * y^2 + b * y + c = 0) /\
          ~(x = y)
          ==> (a * x * y = c) /\ (a * (x + y) + b = 0)|});
  print_bool
    (grobner_decide
     {%fol|(y_1 = 2 * y_3) /\
      (y_2 = 2 * y_4) /\
      (y_1 * y_3 = y_2 * y_4)
      ==> (y_1^2 = y_2^2)|});
  print_bool
    (grobner_decide
     {%fol|(x1 = u3) /\
      (x1 * (u2 - u1) = x2 * u3) /\
      (x4 * (x2 - u1) = x1 * (x3 - u1)) /\
      (x3 * u3 = x4 * u2) /\
      ~(u1 = 0) /\
      ~(u3 = 0)
      ==> (x3^2 + x4^2 = (u2 - x3)^2 + (u3 - x4)^2)|});
  print_bool
    (grobner_decide
     {%fol|(u1 * x1 - u1 * u3 = 0) /\
      (u3 * x2 - (u2 - u1) * x1 = 0) /\
      (x1 * x4 - (x2 - u1) * x3 - u1 * x1 = 0) /\
      (u3 * x4 - u2 * x3 = 0) /\
      ~(u1 = 0) /\
      ~(u3 = 0)
      ==> (2 * u2 * x4 + 2 * u3 * x3 - u3^2 - u2^2 = 0)|});
  (*** Checking resultants (in one direction) ***)
  print_bool
    (grobner_decide
    {%fol|a * x^2 + b * x + c = 0 /\ 2 * a * x + b = 0
     ==> 4*a^2*c-b^2*a = 0|});
  print_bool
    (grobner_decide
    {%fol|a * x^2 + b * x + c = 0 /\ d * x + e = 0
     ==> d^2*c-e*d*b+a*e^2 = 0|});
  print_bool
    (grobner_decide
    {%fol|a * x^2 + b * x + c = 0 /\ d * x^2 + e * x + f = 0
     ==> d^2*c^2-2*d*c*a*f+a^2*f^2-e*d*b*c-e*b*a*f+a*e^2*c+f*d*b^2 = 0|});
  (****** Seems a bit too lengthy?

  grobner_decide
  {%fol|a * x^3 + b * x^2 + c * x + d = 0 /\ e * x^2 + f * x + g = 0
   ==>
  e^3*d^2+3*e*d*g*a*f-2*e^2*d*g*b-g^2*a*f*b+g^2*e*b^2-f*e^2*c*d+f^2*c*g*a-f*e*c*
  g*b+f^2*e*b*d-f^3*a*d+g*e^2*c^2-2*e*c*a*g^2+a^2*g^3 = 0|};;

   ********)

  (********** Works correctly, but it's lengthy

  grobner_decide
   {%fol| (x1 - x0)^2 + (y1 - y0)^2 =
     (x2 - x0)^2 + (y2 - y0)^2 /\
     (x2 - x0)^2 + (y2 - y0)^2 =
     (x3 - x0)^2 + (y3 - y0)^2 /\
     (x1 - x0')^2 + (y1 - y0')^2 =
     (x2 - x0')^2 + (y2 - y0')^2 /\
     (x2 - x0')^2 + (y2 - y0')^2 =
     (x3 - x0')^2 + (y3 - y0')^2
     ==> x0 = x0' /\ y0 = y0'|};;

         **** Corrected with non-isotropy conditions; even lengthier

  grobner_decide
   {%fol|(x1 - x0)^2 + (y1 - y0)^2 =
    (x2 - x0)^2 + (y2 - y0)^2 /\
    (x2 - x0)^2 + (y2 - y0)^2 =
    (x3 - x0)^2 + (y3 - y0)^2 /\
    (x1 - x0')^2 + (y1 - y0')^2 =
    (x2 - x0')^2 + (y2 - y0')^2 /\
    (x2 - x0')^2 + (y2 - y0')^2 =
    (x3 - x0')^2 + (y3 - y0')^2 /\
    ~((x1 - x0)^2 + (y1 - y0)^2 = 0) /\
    ~((x1 - x0')^2 + (y1 - y0')^2 = 0)
    ==> x0 = x0' /\ y0 = y0'|};;

          *** Maybe this is more efficient? (No?)

  grobner_decide
   {%fol|(x1 - x0)^2 + (y1 - y0)^2 = d /\
    (x2 - x0)^2 + (y2 - y0)^2 = d /\
    (x3 - x0)^2 + (y3 - y0)^2 = d /\
    (x1 - x0')^2 + (y1 - y0')^2 = e /\
    (x2 - x0')^2 + (y2 - y0')^2 = e /\
    (x3 - x0')^2 + (y3 - y0')^2 = e /\
    ~(d = 0) /\ ~(e = 0)
    ==> x0 = x0' /\ y0 = y0'|};;

  ***********)

  (* ------------------------------------------------------------------------- *)
  (* Inversion of homographic function (from Gosper's CF notes).               *)
  (* ------------------------------------------------------------------------- *)
  print_bool
    (grobner_decide
     {%fol|y * (c * x + d) = a * x + b ==> x * (c * y - a) = b - d * y|});
  (* ------------------------------------------------------------------------- *)
  (* Manual "sums of squares" for 0 <= a /\ a <= b ==> a^3 <= b^3.             *)
  (* ------------------------------------------------------------------------- *)
  print_fol_formula
    (complex_qelim
     {%fol|forall a b c d e.
         a = c^2 /\ b = a + d^2 /\ (b^3 - a^3) * e^2 + 1 = 0
         ==> (a * d * e)^2 + (c^2 * d * e)^2 + (c * d^2 * e)^2 + (b * d * e)^2 + 1 =
            0|});
  print_bool
    (grobner_decide
      {%fol|a = c^2 /\ b = a + d^2 /\ (b^3 - a^3) * e^2 + 1 = 0
        ==> (a * d * e)^2 + (c^2 * d * e)^2 + (c * d^2 * e)^2 + (b * d * e)^2 + 1 =
            0|});
  (* ------------------------------------------------------------------------- *)
  (* Special case of a = 1, i.e. 1 <= b ==> 1 <= b^3                           *)
  (* ------------------------------------------------------------------------- *)
  print_fol_formula
    (complex_qelim
     {%fol|forall b d e.
         b = 1 + d^2 /\ (b^3 - 1) * e^2 + 1 = 0
         ==> 2 * (d * e)^2 + (d^2 * e)^2 + (b * d * e)^2 + 1 = 0|});
  print_bool
    (grobner_decide
      {%fol|b = 1 + d^2 /\ (b^3 - 1) * e^2 + 1 = 0
        ==> 2 * (d * e)^2 + (d^2 * e)^2 + (b * d * e)^2 + 1 =  0|});
  (* ------------------------------------------------------------------------- *)
  (* Converse, 0 <= a /\ a^3 <= b^3 ==> a <= b                                 *)
  (*                                                                           *)
  (* This derives b <= 0, but not a full solution.                             *)
  (* ------------------------------------------------------------------------- *)
  print_bool
    (grobner_decide
     {%fol|a = c^2 /\ b^3 = a^3 + d^2 /\ (b - a) * e^2 + 1 = 0
       ==> c^2 * b + a^2 + b^2 + (e * d)^2 = 0|});
  (* ------------------------------------------------------------------------- *)
  (* Here are further steps towards a solution, step-by-step.                  *)
  (* ------------------------------------------------------------------------- *)
  print_bool
    (grobner_decide
     {%fol|a = c^2 /\ b^3 = a^3 + d^2 /\ (b - a) * e^2 + 1 = 0
       ==> c^2 * b = -(a^2 + b^2 + (e * d)^2)|});
  print_bool
    (grobner_decide
     {%fol|a = c^2 /\ b^3 = a^3 + d^2 /\ (b - a) * e^2 + 1 = 0
       ==> c^6 * b^3 = -(a^2 + b^2 + (e * d)^2)^3|});
  print_bool
    (grobner_decide
     {%fol|a = c^2 /\ b^3 = a^3 + d^2 /\ (b - a) * e^2 + 1 = 0
       ==> c^6 * (c^6 + d^2) + (a^2 + b^2 + (e * d)^2)^3 = 0|});
  (* ------------------------------------------------------------------------- *)
  (* A simpler one is ~(x < y /\ y < x), i.e. x < y ==> x <= y.                *)
  (*                                                                           *)
  (* Yet even this isn't completed!                                            *)
  (* ------------------------------------------------------------------------- *)
  print_bool
    (grobner_decide
     {%fol|(y - x) * s^2 = 1 /\ (x - y) * t^2 = 1 ==> s^2 + t^2 = 0|});
  (* ------------------------------------------------------------------------- *)
  (* Inspired by Cardano's formula for a cubic. This actually works worse than *)
  (* with naive quantifier elimination (of course it's false...)               *)
  (* ------------------------------------------------------------------------- *)

  (******

  grobner_decide
   {%fol|t - u = n /\ 27 * t * u = m^3 /\
     ct^3 = t /\ cu^3 = u /\
     x = ct - cu
     ==> x^3 + m * x = n|};;

  ***********)
  [%expect {|
    3 basis elements and 3 pairs
    3 basis elements and 2 pairs
    true3 basis elements and 3 pairs
    3 basis elements and 2 pairs
    4 basis elements and 4 pairs
    4 basis elements and 3 pairs
    4 basis elements and 2 pairs
    4 basis elements and 1 pairs
    4 basis elements and 0 pairs
    false4 basis elements and 6 pairs
    5 basis elements and 9 pairs
    5 basis elements and 8 pairs
    6 basis elements and 12 pairs
    7 basis elements and 17 pairs
    8 basis elements and 23 pairs
    9 basis elements and 30 pairs
    9 basis elements and 29 pairs
    9 basis elements and 28 pairs
    10 basis elements and 36 pairs
    11 basis elements and 45 pairs
    12 basis elements and 55 pairs
    13 basis elements and 66 pairs
    13 basis elements and 65 pairs
    14 basis elements and 77 pairs
    15 basis elements and 90 pairs
    16 basis elements and 104 pairs
    16 basis elements and 103 pairs
    17 basis elements and 118 pairs
    18 basis elements and 134 pairs
    19 basis elements and 151 pairs
    4 basis elements and 6 pairs
    5 basis elements and 9 pairs
    5 basis elements and 8 pairs
    6 basis elements and 12 pairs
    7 basis elements and 17 pairs
    8 basis elements and 23 pairs
    9 basis elements and 30 pairs
    10 basis elements and 38 pairs
    11 basis elements and 47 pairs
    12 basis elements and 57 pairs
    13 basis elements and 68 pairs
    14 basis elements and 80 pairs
    15 basis elements and 93 pairs
    15 basis elements and 92 pairs
    16 basis elements and 106 pairs
    17 basis elements and 121 pairs
    18 basis elements and 137 pairs
    18 basis elements and 136 pairs
    19 basis elements and 153 pairs
    20 basis elements and 171 pairs
    21 basis elements and 190 pairs
    true4 basis elements and 6 pairs
    5 basis elements and 9 pairs
    5 basis elements and 8 pairs
    6 basis elements and 12 pairs
    7 basis elements and 17 pairs
    8 basis elements and 23 pairs
    9 basis elements and 30 pairs
    9 basis elements and 29 pairs
    9 basis elements and 28 pairs
    10 basis elements and 36 pairs
    11 basis elements and 45 pairs
    12 basis elements and 55 pairs
    13 basis elements and 66 pairs
    13 basis elements and 65 pairs
    14 basis elements and 77 pairs
    15 basis elements and 90 pairs
    16 basis elements and 104 pairs
    16 basis elements and 103 pairs
    17 basis elements and 118 pairs
    18 basis elements and 134 pairs
    19 basis elements and 151 pairs
    4 basis elements and 6 pairs
    5 basis elements and 9 pairs
    5 basis elements and 8 pairs
    6 basis elements and 12 pairs
    7 basis elements and 17 pairs
    8 basis elements and 23 pairs
    9 basis elements and 30 pairs
    10 basis elements and 38 pairs
    11 basis elements and 47 pairs
    12 basis elements and 57 pairs
    13 basis elements and 68 pairs
    14 basis elements and 80 pairs
    15 basis elements and 93 pairs
    15 basis elements and 92 pairs
    16 basis elements and 106 pairs
    17 basis elements and 121 pairs
    18 basis elements and 137 pairs
    18 basis elements and 136 pairs
    19 basis elements and 153 pairs
    20 basis elements and 171 pairs
    21 basis elements and 190 pairs
    (<<true>>, true)3 basis elements and 3 pairs
    3 basis elements and 2 pairs
    true3 basis elements and 3 pairs
    3 basis elements and 2 pairs
    4 basis elements and 4 pairs
    4 basis elements and 3 pairs
    4 basis elements and 2 pairs
    4 basis elements and 1 pairs
    4 basis elements and 0 pairs
    false4 basis elements and 6 pairs
    5 basis elements and 9 pairs
    5 basis elements and 8 pairs
    6 basis elements and 12 pairs
    7 basis elements and 17 pairs
    8 basis elements and 23 pairs
    9 basis elements and 30 pairs
    9 basis elements and 29 pairs
    9 basis elements and 28 pairs
    10 basis elements and 36 pairs
    11 basis elements and 45 pairs
    12 basis elements and 55 pairs
    13 basis elements and 66 pairs
    13 basis elements and 65 pairs
    14 basis elements and 77 pairs
    15 basis elements and 90 pairs
    16 basis elements and 104 pairs
    16 basis elements and 103 pairs
    17 basis elements and 118 pairs
    18 basis elements and 134 pairs
    19 basis elements and 151 pairs
    4 basis elements and 6 pairs
    5 basis elements and 9 pairs
    5 basis elements and 8 pairs
    6 basis elements and 12 pairs
    7 basis elements and 17 pairs
    8 basis elements and 23 pairs
    9 basis elements and 30 pairs
    10 basis elements and 38 pairs
    11 basis elements and 47 pairs
    12 basis elements and 57 pairs
    13 basis elements and 68 pairs
    14 basis elements and 80 pairs
    15 basis elements and 93 pairs
    15 basis elements and 92 pairs
    16 basis elements and 106 pairs
    17 basis elements and 121 pairs
    18 basis elements and 137 pairs
    18 basis elements and 136 pairs
    19 basis elements and 153 pairs
    20 basis elements and 171 pairs
    21 basis elements and 190 pairs
    true4 basis elements and 6 pairs
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
    true7 basis elements and 21 pairs
    7 basis elements and 20 pairs
    7 basis elements and 19 pairs
    8 basis elements and 25 pairs
    8 basis elements and 24 pairs
    8 basis elements and 23 pairs
    8 basis elements and 22 pairs
    9 basis elements and 29 pairs
    9 basis elements and 28 pairs
    9 basis elements and 27 pairs
    10 basis elements and 35 pairs
    11 basis elements and 44 pairs
    11 basis elements and 43 pairs
    12 basis elements and 53 pairs
    13 basis elements and 64 pairs
    14 basis elements and 76 pairs
    15 basis elements and 89 pairs
    15 basis elements and 88 pairs
    16 basis elements and 102 pairs
    true7 basis elements and 21 pairs
    7 basis elements and 20 pairs
    7 basis elements and 19 pairs
    8 basis elements and 25 pairs
    9 basis elements and 32 pairs
    9 basis elements and 31 pairs
    9 basis elements and 30 pairs
    10 basis elements and 38 pairs
    11 basis elements and 47 pairs
    11 basis elements and 46 pairs
    12 basis elements and 56 pairs
    13 basis elements and 67 pairs
    13 basis elements and 66 pairs
    14 basis elements and 78 pairs
    15 basis elements and 91 pairs
    16 basis elements and 105 pairs
    17 basis elements and 120 pairs
    17 basis elements and 119 pairs
    18 basis elements and 135 pairs
    true3 basis elements and 3 pairs
    4 basis elements and 5 pairs
    5 basis elements and 8 pairs
    6 basis elements and 12 pairs
    6 basis elements and 11 pairs
    7 basis elements and 16 pairs
    8 basis elements and 22 pairs
    9 basis elements and 29 pairs
    9 basis elements and 28 pairs
    9 basis elements and 27 pairs
    10 basis elements and 35 pairs
    10 basis elements and 34 pairs
    10 basis elements and 33 pairs
    10 basis elements and 32 pairs
    10 basis elements and 31 pairs
    11 basis elements and 40 pairs
    11 basis elements and 39 pairs
    11 basis elements and 38 pairs
    11 basis elements and 37 pairs
    11 basis elements and 36 pairs
    11 basis elements and 35 pairs
    true3 basis elements and 3 pairs
    4 basis elements and 5 pairs
    5 basis elements and 8 pairs
    6 basis elements and 12 pairs
    6 basis elements and 11 pairs
    7 basis elements and 16 pairs
    7 basis elements and 15 pairs
    8 basis elements and 21 pairs
    9 basis elements and 28 pairs
    10 basis elements and 36 pairs
    11 basis elements and 45 pairs
    12 basis elements and 55 pairs
    13 basis elements and 66 pairs
    13 basis elements and 65 pairs
    14 basis elements and 77 pairs
    15 basis elements and 90 pairs
    16 basis elements and 104 pairs
    16 basis elements and 103 pairs
    16 basis elements and 102 pairs
    16 basis elements and 101 pairs
    16 basis elements and 100 pairs
    true3 basis elements and 3 pairs
    4 basis elements and 5 pairs
    5 basis elements and 8 pairs
    6 basis elements and 12 pairs
    7 basis elements and 17 pairs
    8 basis elements and 23 pairs
    9 basis elements and 30 pairs
    10 basis elements and 38 pairs
    11 basis elements and 47 pairs
    12 basis elements and 57 pairs
    13 basis elements and 68 pairs
    14 basis elements and 80 pairs
    15 basis elements and 93 pairs
    16 basis elements and 107 pairs
    17 basis elements and 122 pairs
    18 basis elements and 138 pairs
    19 basis elements and 155 pairs
    20 basis elements and 173 pairs
    20 basis elements and 172 pairs
    21 basis elements and 191 pairs
    21 basis elements and 190 pairs
    22 basis elements and 210 pairs
    23 basis elements and 231 pairs
    24 basis elements and 253 pairs
    24 basis elements and 252 pairs
    25 basis elements and 275 pairs
    25 basis elements and 274 pairs
    25 basis elements and 273 pairs
    26 basis elements and 297 pairs
    27 basis elements and 322 pairs
    27 basis elements and 321 pairs
    27 basis elements and 320 pairs
    27 basis elements and 319 pairs
    27 basis elements and 318 pairs
    27 basis elements and 317 pairs
    28 basis elements and 343 pairs
    29 basis elements and 370 pairs
    29 basis elements and 369 pairs
    29 basis elements and 368 pairs
    29 basis elements and 367 pairs
    29 basis elements and 366 pairs
    29 basis elements and 365 pairs
    30 basis elements and 393 pairs
    31 basis elements and 422 pairs
    32 basis elements and 452 pairs
    32 basis elements and 451 pairs
    32 basis elements and 450 pairs
    32 basis elements and 449 pairs
    33 basis elements and 480 pairs
    33 basis elements and 479 pairs
    33 basis elements and 478 pairs
    34 basis elements and 510 pairs
    34 basis elements and 509 pairs
    35 basis elements and 542 pairs
    35 basis elements and 541 pairs
    35 basis elements and 540 pairs
    35 basis elements and 539 pairs
    36 basis elements and 573 pairs
    36 basis elements and 572 pairs
    36 basis elements and 571 pairs
    36 basis elements and 570 pairs
    36 basis elements and 569 pairs
    36 basis elements and 568 pairs
    36 basis elements and 567 pairs
    37 basis elements and 602 pairs
    37 basis elements and 601 pairs
    37 basis elements and 600 pairs
    37 basis elements and 599 pairs
    37 basis elements and 598 pairs
    37 basis elements and 597 pairs
    37 basis elements and 596 pairs
    37 basis elements and 595 pairs
    37 basis elements and 594 pairs
    37 basis elements and 593 pairs
    37 basis elements and 592 pairs
    37 basis elements and 591 pairs
    37 basis elements and 590 pairs
    37 basis elements and 589 pairs
    38 basis elements and 625 pairs
    38 basis elements and 624 pairs
    38 basis elements and 623 pairs
    38 basis elements and 622 pairs
    38 basis elements and 621 pairs
    38 basis elements and 620 pairs
    38 basis elements and 619 pairs
    38 basis elements and 618 pairs
    38 basis elements and 617 pairs
    38 basis elements and 616 pairs
    38 basis elements and 615 pairs
    38 basis elements and 614 pairs
    38 basis elements and 613 pairs
    38 basis elements and 612 pairs
    38 basis elements and 611 pairs
    38 basis elements and 610 pairs
    38 basis elements and 609 pairs
    38 basis elements and 608 pairs
    38 basis elements and 607 pairs
    38 basis elements and 606 pairs
    38 basis elements and 605 pairs
    38 basis elements and 604 pairs
    38 basis elements and 603 pairs
    38 basis elements and 602 pairs
    38 basis elements and 601 pairs
    38 basis elements and 600 pairs
    38 basis elements and 599 pairs
    38 basis elements and 598 pairs
    38 basis elements and 597 pairs
    38 basis elements and 596 pairs
    38 basis elements and 595 pairs
    38 basis elements and 594 pairs
    38 basis elements and 593 pairs
    38 basis elements and 592 pairs
    38 basis elements and 591 pairs
    38 basis elements and 590 pairs
    38 basis elements and 589 pairs
    38 basis elements and 588 pairs
    38 basis elements and 587 pairs
    38 basis elements and 586 pairs
    38 basis elements and 585 pairs
    38 basis elements and 584 pairs
    38 basis elements and 583 pairs
    38 basis elements and 582 pairs
    38 basis elements and 581 pairs
    38 basis elements and 580 pairs
    38 basis elements and 579 pairs
    38 basis elements and 578 pairs
    38 basis elements and 577 pairs
    38 basis elements and 576 pairs
    38 basis elements and 575 pairs
    38 basis elements and 574 pairs
    38 basis elements and 573 pairs
    38 basis elements and 572 pairs
    38 basis elements and 571 pairs
    38 basis elements and 570 pairs
    38 basis elements and 569 pairs
    38 basis elements and 568 pairs
    38 basis elements and 567 pairs
    38 basis elements and 566 pairs
    38 basis elements and 565 pairs
    38 basis elements and 564 pairs
    38 basis elements and 563 pairs
    38 basis elements and 562 pairs
    38 basis elements and 561 pairs
    38 basis elements and 560 pairs
    38 basis elements and 559 pairs
    39 basis elements and 596 pairs
    40 basis elements and 634 pairs
    40 basis elements and 633 pairs
    40 basis elements and 632 pairs
    40 basis elements and 631 pairs
    40 basis elements and 630 pairs
    40 basis elements and 629 pairs
    40 basis elements and 628 pairs
    41 basis elements and 667 pairs
    41 basis elements and 666 pairs
    41 basis elements and 665 pairs
    41 basis elements and 664 pairs
    41 basis elements and 663 pairs
    41 basis elements and 662 pairs
    41 basis elements and 661 pairs
    41 basis elements and 660 pairs
    41 basis elements and 659 pairs
    41 basis elements and 658 pairs
    41 basis elements and 657 pairs
    42 basis elements and 697 pairs
    42 basis elements and 696 pairs
    42 basis elements and 695 pairs
    43 basis elements and 736 pairs
    43 basis elements and 735 pairs
    43 basis elements and 734 pairs
    44 basis elements and 776 pairs
    44 basis elements and 775 pairs
    44 basis elements and 774 pairs
    44 basis elements and 773 pairs
    44 basis elements and 772 pairs
    44 basis elements and 771 pairs
    44 basis elements and 770 pairs
    44 basis elements and 769 pairs
    44 basis elements and 768 pairs
    44 basis elements and 767 pairs
    44 basis elements and 766 pairs
    44 basis elements and 765 pairs
    44 basis elements and 764 pairs
    44 basis elements and 763 pairs
    44 basis elements and 762 pairs
    44 basis elements and 761 pairs
    44 basis elements and 760 pairs
    44 basis elements and 759 pairs
    44 basis elements and 758 pairs
    44 basis elements and 757 pairs
    45 basis elements and 800 pairs
    45 basis elements and 799 pairs
    45 basis elements and 798 pairs
    45 basis elements and 797 pairs
    45 basis elements and 796 pairs
    45 basis elements and 795 pairs
    45 basis elements and 794 pairs
    45 basis elements and 793 pairs
    45 basis elements and 792 pairs
    45 basis elements and 791 pairs
    45 basis elements and 790 pairs
    45 basis elements and 789 pairs
    45 basis elements and 788 pairs
    45 basis elements and 787 pairs
    45 basis elements and 786 pairs
    45 basis elements and 785 pairs
    45 basis elements and 784 pairs
    45 basis elements and 783 pairs
    45 basis elements and 782 pairs
    45 basis elements and 781 pairs
    true2 basis elements and 1 pairs
    true<<true>>4 basis elements and 6 pairs
    4 basis elements and 5 pairs
    4 basis elements and 4 pairs
    true<<true>>3 basis elements and 3 pairs
    3 basis elements and 2 pairs
    true4 basis elements and 6 pairs
    4 basis elements and 5 pairs
    4 basis elements and 4 pairs
    4 basis elements and 3 pairs
    5 basis elements and 6 pairs
    6 basis elements and 10 pairs
    7 basis elements and 15 pairs
    7 basis elements and 14 pairs
    8 basis elements and 20 pairs
    8 basis elements and 19 pairs
    true4 basis elements and 6 pairs
    4 basis elements and 5 pairs
    4 basis elements and 4 pairs
    4 basis elements and 3 pairs
    5 basis elements and 6 pairs
    6 basis elements and 10 pairs
    7 basis elements and 15 pairs
    7 basis elements and 14 pairs
    8 basis elements and 20 pairs
    8 basis elements and 19 pairs
    true4 basis elements and 6 pairs
    4 basis elements and 5 pairs
    4 basis elements and 4 pairs
    4 basis elements and 3 pairs
    5 basis elements and 6 pairs
    6 basis elements and 10 pairs
    7 basis elements and 15 pairs
    7 basis elements and 14 pairs
    8 basis elements and 20 pairs
    8 basis elements and 19 pairs
    true4 basis elements and 6 pairs
    4 basis elements and 5 pairs
    4 basis elements and 4 pairs
    4 basis elements and 3 pairs
    5 basis elements and 6 pairs
    6 basis elements and 10 pairs
    7 basis elements and 15 pairs
    7 basis elements and 14 pairs
    8 basis elements and 20 pairs
    8 basis elements and 19 pairs
    true3 basis elements and 3 pairs
    4 basis elements and 5 pairs
    5 basis elements and 8 pairs
    6 basis elements and 12 pairs
    7 basis elements and 17 pairs
    7 basis elements and 16 pairs
    true
    |}]
;;

(* ------------------------------------------------------------------------- *)
(* For looking at things it's nice to map back to normal term.               *)
(* ------------------------------------------------------------------------- *)

(*****

let term_of_varpow vars (x,k) =
  if k = 1 then Var x else Fn("^",[Var x; mk_numeral(Int k)]);;

let term_of_varpows vars lis =
  let tms = filter (fun (a,b) -> b <> 0) (zip vars lis) in
  end_itlist (fun s t -> Fn("*",[s;t])) (map (term_of_varpow vars) tms);;

let term_of_monomial vars (c,m) =
  if forall (fun x -> x = 0) m then mk_numeral c
  else if c =/ Int 1 then term_of_varpows vars m
  else Fn("*",[mk_numeral c; term_of_varpows vars m]);;

let term_of_poly vars pol =
  end_itlist (fun s t -> Fn("+",[s;t])) (map (term_of_monomial vars) pol);;

let grobner_basis vars pols =
  map (term_of_poly vars) (groebner (map (mpolyatom vars) pols));;

*****)
