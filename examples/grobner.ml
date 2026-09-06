(* Interactive examples from grobner.ml, lifted out of the source.  Not compiled: these are meant to be
   pasted into a toplevel that has opened Atp.All. *)

grobner_decide
  {%fol|a^2 = 2 /\ x^2 + a*x + 1 = 0 ==> x^4 + 1 = 0|};;

grobner_decide
  {%fol|a^2 = 2 /\ x^2 + a*x + 1 = 0 ==> x^4 + 2 = 0|};;

grobner_decide
  {%fol|(a * x^2 + b * x + c = 0) /\
   (a * y^2 + b * y + c = 0) /\
   ~(x = y)
   ==> (a * x * y = c) /\ (a * (x + y) + b = 0)|};;

(* ------------------------------------------------------------------------- *)
(* Compare with earlier procedure.                                           *)
(* ------------------------------------------------------------------------- *)

let fm =
  {%fol|(a * x^2 + b * x + c = 0) /\
    (a * y^2 + b * y + c = 0) /\
    ~(x = y)
    ==> (a * x * y = c) /\ (a * (x + y) + b = 0)|} in
time complex_qelim (generalize fm),time grobner_decide fm;;

(* ------------------------------------------------------------------------- *)
(* More tests.                                                               *)
(* ------------------------------------------------------------------------- *)

time grobner_decide  {%fol|a^2 = 2 /\ x^2 + a*x + 1 = 0 ==> x^4 + 1 = 0|};;

time grobner_decide  {%fol|a^2 = 2 /\ x^2 + a*x + 1 = 0 ==> x^4 + 2 = 0|};;

time grobner_decide {%fol|(a * x^2 + b * x + c = 0) /\
      (a * y^2 + b * y + c = 0) /\
      ~(x = y)
      ==> (a * x * y = c) /\ (a * (x + y) + b = 0)|};;

time grobner_decide
 {%fol|(y_1 = 2 * y_3) /\
  (y_2 = 2 * y_4) /\
  (y_1 * y_3 = y_2 * y_4)
  ==> (y_1^2 = y_2^2)|};;

time grobner_decide
 {%fol|(x1 = u3) /\
  (x1 * (u2 - u1) = x2 * u3) /\
  (x4 * (x2 - u1) = x1 * (x3 - u1)) /\
  (x3 * u3 = x4 * u2) /\
  ~(u1 = 0) /\
  ~(u3 = 0)
  ==> (x3^2 + x4^2 = (u2 - x3)^2 + (u3 - x4)^2)|};;

time grobner_decide
 {%fol|(u1 * x1 - u1 * u3 = 0) /\
  (u3 * x2 - (u2 - u1) * x1 = 0) /\
  (x1 * x4 - (x2 - u1) * x3 - u1 * x1 = 0) /\
  (u3 * x4 - u2 * x3 = 0) /\
  ~(u1 = 0) /\
  ~(u3 = 0)
  ==> (2 * u2 * x4 + 2 * u3 * x3 - u3^2 - u2^2 = 0)|};;

(*** Checking resultants (in one direction) ***)

time grobner_decide
{%fol|a * x^2 + b * x + c = 0 /\ 2 * a * x + b = 0
 ==> 4*a^2*c-b^2*a = 0|};;

time grobner_decide
{%fol|a * x^2 + b * x + c = 0 /\ d * x + e = 0
 ==> d^2*c-e*d*b+a*e^2 = 0|};;


time grobner_decide
{%fol|a * x^2 + b * x + c = 0 /\ d * x^2 + e * x + f = 0
 ==> d^2*c^2-2*d*c*a*f+a^2*f^2-e*d*b*c-e*b*a*f+a*e^2*c+f*d*b^2 = 0|};;

(****** Seems a bit too lengthy?

time grobner_decide
{%fol|a * x^3 + b * x^2 + c * x + d = 0 /\ e * x^2 + f * x + g = 0
 ==>
e^3*d^2+3*e*d*g*a*f-2*e^2*d*g*b-g^2*a*f*b+g^2*e*b^2-f*e^2*c*d+f^2*c*g*a-f*e*c*
g*b+f^2*e*b*d-f^3*a*d+g*e^2*c^2-2*e*c*a*g^2+a^2*g^3 = 0|};;

 ********)

(********** Works correctly, but it's lengthy

time grobner_decide
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

time grobner_decide
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

time grobner_decide
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

time grobner_decide
 {%fol|y * (c * x + d) = a * x + b ==> x * (c * y - a) = b - d * y|};;

(* ------------------------------------------------------------------------- *)
(* Manual "sums of squares" for 0 <= a /\ a <= b ==> a^3 <= b^3.             *)
(* ------------------------------------------------------------------------- *)

time complex_qelim
 {%fol|forall a b c d e.
     a = c^2 /\ b = a + d^2 /\ (b^3 - a^3) * e^2 + 1 = 0
     ==> (a * d * e)^2 + (c^2 * d * e)^2 + (c * d^2 * e)^2 + (b * d * e)^2 + 1 =
        0|};;

time grobner_decide
  {%fol|a = c^2 /\ b = a + d^2 /\ (b^3 - a^3) * e^2 + 1 = 0
    ==> (a * d * e)^2 + (c^2 * d * e)^2 + (c * d^2 * e)^2 + (b * d * e)^2 + 1 =
        0|};;

(* ------------------------------------------------------------------------- *)
(* Special case of a = 1, i.e. 1 <= b ==> 1 <= b^3                           *)
(* ------------------------------------------------------------------------- *)

time complex_qelim
 {%fol|forall b d e.
     b = 1 + d^2 /\ (b^3 - 1) * e^2 + 1 = 0
     ==> 2 * (d * e)^2 + (d^2 * e)^2 + (b * d * e)^2 + 1 = 0|};;

time grobner_decide
  {%fol|b = 1 + d^2 /\ (b^3 - 1) * e^2 + 1 = 0
    ==> 2 * (d * e)^2 + (d^2 * e)^2 + (b * d * e)^2 + 1 =  0|};;

(* ------------------------------------------------------------------------- *)
(* Converse, 0 <= a /\ a^3 <= b^3 ==> a <= b                                 *)
(*                                                                           *)
(* This derives b <= 0, but not a full solution.                             *)
(* ------------------------------------------------------------------------- *)

time grobner_decide
 {%fol|a = c^2 /\ b^3 = a^3 + d^2 /\ (b - a) * e^2 + 1 = 0
   ==> c^2 * b + a^2 + b^2 + (e * d)^2 = 0|};;

(* ------------------------------------------------------------------------- *)
(* Here are further steps towards a solution, step-by-step.                  *)
(* ------------------------------------------------------------------------- *)

time grobner_decide
 {%fol|a = c^2 /\ b^3 = a^3 + d^2 /\ (b - a) * e^2 + 1 = 0
   ==> c^2 * b = -(a^2 + b^2 + (e * d)^2)|};;

time grobner_decide
 {%fol|a = c^2 /\ b^3 = a^3 + d^2 /\ (b - a) * e^2 + 1 = 0
   ==> c^6 * b^3 = -(a^2 + b^2 + (e * d)^2)^3|};;

time grobner_decide
 {%fol|a = c^2 /\ b^3 = a^3 + d^2 /\ (b - a) * e^2 + 1 = 0
   ==> c^6 * (c^6 + d^2) + (a^2 + b^2 + (e * d)^2)^3 = 0|};;

(* ------------------------------------------------------------------------- *)
(* A simpler one is ~(x < y /\ y < x), i.e. x < y ==> x <= y.                *)
(*                                                                           *)
(* Yet even this isn't completed!                                            *)
(* ------------------------------------------------------------------------- *)

time grobner_decide
 {%fol|(y - x) * s^2 = 1 /\ (x - y) * t^2 = 1 ==> s^2 + t^2 = 0|};;

(* ------------------------------------------------------------------------- *)
(* Inspired by Cardano's formula for a cubic. This actually works worse than *)
(* with naive quantifier elimination (of course it's false...)               *)
(* ------------------------------------------------------------------------- *)

(******

time grobner_decide
 {%fol|t - u = n /\ 27 * t * u = m^3 /\
   ct^3 = t /\ cu^3 = u /\
   x = ct - cu
   ==> x^3 + m * x = n|};;

***********)
