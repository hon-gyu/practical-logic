(* Interactive examples from cooper.ml, lifted out of the source by
   tools/migrate_to_modules.py.  Not compiled: these are meant to be
   pasted into a toplevel that has opened Atp.All. *)

integer_qelim {%fol|forall x y. ~(2 * x + 1 = 2 * y)|};;

integer_qelim {%fol|forall x. exists y. 2 * y <= x /\ x < 2 * (y + 1)|};;

integer_qelim {%fol|exists x y. 4 * x - 6 * y = 1|};;

integer_qelim {%fol|forall x. ~divides(2,x) /\ divides(3,x-1) <=>
                          divides(12,x-1) \/ divides(12,x-7)|};;

integer_qelim {%fol|forall x. b < x ==> a <= x|};;

(* ---- *)

natural_qelim {%fol|forall d. exists x y. 3 * x + 5 * y = d|};;
integer_qelim {%fol|forall d. exists x y. 3 * x + 5 * y = d|};;
natural_qelim {%fol|forall d. d >= 8 ==> exists x y. 3 * x + 5 * y = d|};;
natural_qelim {%fol|forall d. exists x y. 3 * x - 5 * y = d|};;

(* ------------------------------------------------------------------------- *)
(* Other tests, not in the main text.                                        *)
(* ------------------------------------------------------------------------- *)

integer_qelim {%fol|exists x y. x > 0 /\ y >= 0 /\ 3 * x - 5 * y = 1|};;

integer_qelim {%fol|exists x y z. 4 * x - 6 * y = 1|};;

integer_qelim {%fol|forall x. a < 3 * x ==> b < 3 * x|};;

time integer_qelim {%fol|forall x y. x <= y ==> 2 * x + 1 < 2 * y|};;

time integer_qelim {%fol|(exists d. y = 65 * d) ==> (exists d. y = 5 * d)|};;

time integer_qelim
  {%fol|forall y. (exists d. y = 65 * d) ==> (exists d. y = 5 * d)|};;

time integer_qelim {%fol|forall x y. ~(2 * x + 1 = 2 * y)|};;

time integer_qelim
  {%fol|forall x y z. (2 * x + 1 = 2 * y) ==> x + y + z > 129|};;

time integer_qelim {%fol|forall x. a < x ==> b < x|};;

time integer_qelim {%fol|forall x. a <= x ==> b < x|};;

(* ------------------------------------------------------------------------- *)
(* Formula examples from Cooper's paper.                                     *)
(* ------------------------------------------------------------------------- *)

time integer_qelim {%fol|forall a b. exists x. a < 20 * x /\ 20 * x < b|};;

time integer_qelim {%fol|exists x. a < 20 * x /\ 20 * x < b|};;

time integer_qelim {%fol|forall b. exists x. a < 20 * x /\ 20 * x < b|};;

time integer_qelim
  {%fol|forall a. exists b. a < 4 * b + 3 * a \/ (~(a < b) /\ a > b + 1)|};;

time integer_qelim
  {%fol|exists y. forall x. x + 5 * y > 1 /\ 13 * x - y > 1 /\ x + 2 < 0|};;

(* ------------------------------------------------------------------------- *)
(* More of my own.                                                           *)
(* ------------------------------------------------------------------------- *)

time integer_qelim {%fol|forall x y. x >= 0 /\ y >= 0
                  ==> 12 * x - 8 * y < 0 \/ 12 * x - 8 * y > 2|};;

time integer_qelim {%fol|exists x y. 5 * x + 3 * y = 1|};;

time integer_qelim {%fol|exists x y. 5 * x + 10 * y = 1|};;

time integer_qelim {%fol|exists x y. x >= 0 /\ y >= 0 /\ 5 * x - 6 * y = 1|};;


time integer_qelim {%fol|exists w x y z. 2 * w + 3 * x + 4 * y + 5 * z = 1|};;

time integer_qelim {%fol|exists x y. x >= 0 /\ y >= 0 /\ 5 * x - 3 * y = 1|};;

time integer_qelim {%fol|exists x y. x >= 0 /\ y >= 0 /\ 3 * x - 5 * y = 1|};;

time integer_qelim {%fol|exists x y. x >= 0 /\ y >= 0 /\ 6 * x - 3 * y = 1|};;

time integer_qelim
  {%fol|forall x y. ~(x = 0) ==> 5 * y < 6 * x \/ 5 * y > 6 * x|};;

time integer_qelim
  {%fol|forall x y. ~divides(5,x) /\ ~divides(6,y) ==> ~(6 * x = 5 * y)|};;

time integer_qelim {%fol|forall x y. ~divides(5,x) ==> ~(6 * x = 5 * y)|};;

time integer_qelim {%fol|forall x y. ~(6 * x = 5 * y)|};;

time integer_qelim {%fol|forall x y. 6 * x = 5 * y ==> exists d. y = 3 * d|};;

time integer_qelim {%fol|6 * x = 5 * y ==> exists d. y = 3 * d|};;

(* ------------------------------------------------------------------------- *)
(* Positive variant of the Bezout theorem (see the exercise).                *)
(* ------------------------------------------------------------------------- *)

time integer_qelim
  {%fol|forall z. z > 7 ==> exists x y. x >= 0 /\ y >= 0 /\ 3 * x + 5 * y = z|};;

time integer_qelim
  {%fol|forall z. z > 2 ==> exists x y. x >= 0 /\ y >= 0 /\ 3 * x + 5 * y = z|};;

time integer_qelim
  {%fol|forall z.
        z <= 7
        ==> ((exists x y. x >= 0 /\ y >= 0 /\ 3 * x + 5 * y = z) <=>
             ~(exists x y. x >= 0 /\ y >= 0 /\ 3 * x + 5 * y = 7 - z))|};;

(* ------------------------------------------------------------------------- *)
(* Basic result about congruences.                                           *)
(* ------------------------------------------------------------------------- *)

time integer_qelim
  {%fol|forall x. ~divides(2,x) /\ divides(3,x-1) <=>
              divides(12,x-1) \/ divides(12,x-7)|};;

time integer_qelim
  {%fol|forall x. ~(exists m. x = 2 * m) /\ (exists m. x = 3 * m + 1) <=>
              (exists m. x = 12 * m + 1) \/ (exists m. x = 12 * m + 7)|};;

(* ------------------------------------------------------------------------- *)
(* Something else.                                                           *)
(* ------------------------------------------------------------------------- *)

time integer_qelim
 {%fol|forall x.
        ~(divides(2,x))
        ==> divides(4,x-1) \/
            divides(8,x-1) \/
            divides(8,x-3) \/
            divides(6,x-1) \/
            divides(14,x-1) \/
            divides(14,x-9) \/
            divides(14,x-11) \/
            divides(24,x-5) \/
            divides(24,x-11)|};;

(* ------------------------------------------------------------------------- *)
(* Testing fix for an earlier version with negative result from formlcm.     *)
(* ------------------------------------------------------------------------- *)

(integer_qelim ** generalize)
  {%fol|a + 2 = b /\ v_3 = b - a + 1 /\ v_2 = b - 2 /\ v_1 = 3 ==> false|};;

(* ------------------------------------------------------------------------- *)
(* Inspired by the Collatz conjecture.                                       *)
(* ------------------------------------------------------------------------- *)

integer_qelim
  {%fol|exists a b. ~(a = 1) /\ ((2 * b = a) \/ (2 * b = 3 * a + 1)) /\ (a = b)|};;

integer_qelim
 {%fol|exists a b. a > 1 /\ b > 1 /\
               ((2 * b = a) \/ (2 * b = 3 * a + 1)) /\
               (a = b)|};;

(***************

integer_qelim
 {%fol|exists a b. a > 1 /\ b > 1 /\
               ((2 * b = a) \/ (2 * b = 3 * a + 1)) /\
               ((2 * a = b) \/ (2 * a = 3 * b + 1))|};;

let fm = dnf
 {%fol|((2 * b = a) \/ (2 * b = 3 * a + 1)) /\
   ((2 * c = b) \/ (2 * c = 3 * b + 1)) /\
   ((2 * d = c) \/ (2 * d = 3 * c + 1)) /\
   ((2 * e = d) \/ (2 * e = 3 * d + 1)) /\
   ((2 * f = e) \/ (2 * f = 3 * e + 1)) /\
   (f = a)|};;

let fms =
  map (itlist (fun x p -> Exists(x,And(Atom(R(">",[Var x; Fn("1",[])])),p)))
              ["b"; "c"; "d"; "e"; "f"])
      (disjuncts fm);;

let fm = el 15 fms;;
integer_qelim fm;;

******************)

(* ------------------------------------------------------------------------- *)
(* Bob Constable's "stamp problem".                                          *)
(* ------------------------------------------------------------------------- *)

integer_qelim
  {%fol|forall x. x >= 8 ==> exists u v. u >= 0 /\ v >= 0 /\ x = 3 * u + 5 * v|};;

integer_qelim
  {%fol|exists l.
        forall x. x >= l
                  ==> exists u v. u >= 0 /\ v >= 0 /\ x = 3 * u + 5 * v|};;

integer_qelim
  {%fol|exists l.
        forall x. x >= l
                  ==> exists u v. u >= 0 /\ v >= 0 /\ x = 3 * u + 7 * v|};;

(************ These seem to take a while --- the second may not be feasible
              although the first is not so bad.

integer_qelim
  {%fol|exists l.
        forall x. x >= l
                  ==> exists u v. u >= 0 /\ v >= 0 /\ x = 3 * u + 8 * v|};;

integer_qelim
  {%fol|exists l.
        forall x. x >= l
                  ==> exists u v. u >= 0 /\ v >= 0 /\ x = 7 * u + 8 * v|};;

****************)

(* ------------------------------------------------------------------------- *)
(* Example from reciprocal mult: (2622 * x)>>16 = x/100 within a range.      *)
(* ------------------------------------------------------------------------- *)

(*********
integer_qelim
  {%fol|forall x q1 q2 r1 r2.
        x < 4699 /\
        2622 * x = 65536 * q1 + r1 /\ 0 <= q1 /\ 0 <= r1 /\ r1 < 65536 /\
        x = 100 * q2 + r2 /\ 0 <= q2 /\ 0 <= r2 /\ r2 < 100
        ==> q1 = q2|};;
 *********)

(* ------------------------------------------------------------------------- *)
(* Yet more.                                                                 *)
(* ------------------------------------------------------------------------- *)

integer_qelim
  {%fol|forall x y.
        (exists d. x + y = 2 * d) <=>
        ((exists d. x = 2 * d) <=> (exists d. y = 2 * d))|};;

(**** Landau trick! Is it too slow?

integer_qelim
 {%fol|forall n.
     0 < n /\ n < 2400
       ==> n <= 2 /\ 2 <= 2 * n \/
           n <= 3 /\ 3 <= 2 * n \/
           n <= 5 /\ 5 <= 2 * n \/
           n <= 7 /\ 7 <= 2 * n \/
           n <= 13 /\ 13 <= 2 * n \/
           n <= 23 /\ 23 <= 2 * n \/
           n <= 43 /\ 43 <= 2 * n \/
           n <= 83 /\ 83 <= 2 * n \/
           n <= 163 /\ 163 <= 2 * n \/
           n <= 317 /\ 317 <= 2 * n \/
           n <= 631 /\ 631 <= 2 * n \/
           n <= 1259 /\ 1259 <= 2 * n \/
           n <= 2503 /\ 2503 <= 2 * n|};;

 ****)
