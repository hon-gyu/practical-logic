(* Interactive examples from geom.ml, lifted out of the source.  Not compiled: these are meant to be
   pasted into a toplevel that has opened Atp.All. *)

coordinate {%fol|collinear(a,b,c) ==> collinear(b,a,c)|};;

(* ---- *)

forall (grobner_decide ** invariant_under_translation) coordinations;;

(* ---- *)

forall (grobner_decide ** invariant_under_rotation) coordinations;;

(* ---- *)

real_qelim
 {%fol|forall x y. exists s c. s^2 + c^2 = 1 /\ s * x + c * y = 0|};;

(* ---- *)

forall (grobner_decide ** invariant_under_scaling) coordinations;;

partition (grobner_decide ** invariant_under_shearing) coordinations;;

(* ---- *)

(grobner_decide ** originate)
 {%fol|is_midpoint(m,a,c) /\ perpendicular(a,c,m,b)
   ==> lengths_eq(a,b,b,c)|};;

(* ------------------------------------------------------------------------- *)
(* Parallelogram theorem (Chou's expository example at the start).           *)
(* ------------------------------------------------------------------------- *)

(grobner_decide ** originate)
 {%fol|parallel(a,b,d,c) /\ parallel(a,d,b,c) /\
   is_intersection(e,a,c,b,d)
   ==> lengths_eq(a,e,e,c)|};;

(grobner_decide ** originate)
 {%fol|parallel(a,b,d,c) /\ parallel(a,d,b,c) /\
   is_intersection(e,a,c,b,d) /\ ~collinear(a,b,c)
   ==> lengths_eq(a,e,e,c)|};;

(* ---- *)

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
   ==> collinear(e,f,g)|};;

let vars =
 ["g_y"; "g_x"; "f_y"; "f_x"; "e_y"; "e_x"; "d_y"; "d_x"; "c_y"; "c_x";
  "b_y"; "b_x"; "o_x"]
and zeros = ["a_x"; "a_y"; "o_y"];;

wu simson vars zeros;;

(* ------------------------------------------------------------------------- *)
(* Try without special coordinates.                                          *)
(* ------------------------------------------------------------------------- *)

wu simson (vars @ zeros) [];;

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
   ==> collinear(d,e,f)|};;

let vars = ["f_y"; "f_x"; "e_y"; "e_x"; "d_y"; "d_x";
            "b3_y"; "b2_y"; "b1_y"; "a3_x"; "a2_x"; "a1_x"]
and zeros = ["a1_y"; "a2_y"; "a3_y"; "b1_x"; "b2_x"; "b3_x"];;

wu pappus vars zeros;;

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
