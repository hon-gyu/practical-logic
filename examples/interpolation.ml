(* Interactive examples from interpolation.ml, lifted out of the source.  Not compiled: these are meant to be
   pasted into a toplevel that has opened Atp.All. *)

let p = prenex
 {%fol|(forall x. R(x,f(x))) /\ (forall x y. S(x,y) <=> R(x,y) \/ R(y,x))|}
and q = prenex
 {%fol|(forall x y z. S(x,y) /\ S(y,z) ==> T(x,z)) /\ ~T(0,0)|};;

let c = urinterpolate p q;;

meson(Imp(p,c));;
meson(Imp(q,Not c));;

(* ---- *)

let c = uinterpolate p q;;

meson(Imp(p,c));;
meson(Imp(q,Not c));;

(* ---- *)

let p =
 {%fol|(forall x. exists y. R(x,y)) /\
   (forall x y. S(v,x,y) <=> R(x,y) \/ R(y,x))|}
and q =
 {%fol|(forall x y z. S(v,x,y) /\ S(v,y,z) ==> T(x,z)) /\
   (exists u. ~T(u,u))|};;

let c = interpolate p q;;

meson(Imp(p,c));;
meson(Imp(q,Not c));;

(* ---- *)

let p = {%fol|(p ==> q /\ r)|}
and q = {%fol|~((q ==> p) ==> s ==> (p <=> q))|};;

let c = interpolate p q;;

tautology(Imp(And(p,q),False));;

tautology(Imp(p,c));;
tautology(Imp(q,Not c));;

(* ------------------------------------------------------------------------- *)
(* A more interesting example.                                               *)
(* ------------------------------------------------------------------------- *)

let p = {%fol|(forall x. exists y. R(x,y)) /\
          (forall x y. S(x,y) <=> R(x,y) \/ R(y,x))|}
and q = {%fol|(forall x y z. S(x,y) /\ S(y,z) ==> T(x,z)) /\ ~T(u,u)|};;

meson(Imp(And(p,q),False));;

let c = interpolate p q;;

meson(Imp(p,c));;
meson(Imp(q,Not c));;

(* ------------------------------------------------------------------------- *)
(* A variant where u is free in both parts.                                  *)
(* ------------------------------------------------------------------------- *)

let p = {%fol|(forall x. exists y. R(x,y)) /\
          (forall x y. S(x,y) <=> R(x,y) \/ R(y,x)) /\
          (forall v. R(u,v) ==> Q(v,u))|}
and q = {%fol|(forall x y z. S(x,y) /\ S(y,z) ==> T(x,z)) /\ ~T(u,u)|};;

meson(Imp(And(p,q),False));;

let c = interpolate p q;;
meson(Imp(p,c));;
meson(Imp(q,Not c));;

(* ------------------------------------------------------------------------- *)
(* Way of generating examples quite easily (see K&K exercises).              *)
(* ------------------------------------------------------------------------- *)

let test_interp fm =
  let p = generalize(skolemize fm)
  and q = generalize(skolemize(Not fm)) in
  let c = interpolate p q in
  meson(Imp(And(p,q),False)); meson(Imp(p,c)); meson(Imp(q,Not c)); c;;

test_interp {%fol|forall x. P(x) ==> exists y. forall z. P(z) ==> Q(y)|};;

test_interp {%fol|forall y. exists y. forall z. exists a.
                P(a,x,y,z) ==> P(x,y,z,a)|};;

(* ------------------------------------------------------------------------- *)
(* Hintikka's examples.                                                      *)
(* ------------------------------------------------------------------------- *)

let p = {%fol|forall x. L(x,b)|}
and q = {%fol|(forall y. L(b,y) ==> m = y) /\ ~(m = b)|};;

let c = einterpolate p q;;

meson(Imp(p,c));;
meson(Imp(q,Not c));;

let p =
 {%fol|(forall x. A(x) /\ C(x) ==> B(x)) /\ (forall x. D(x) \/ ~D(x) ==> C(x))|}
and q =
 {%fol|~(forall x. E(x) ==> A(x) ==> B(x))|};;

let c = interpolate p q;;
meson(Imp(p,c));;
meson(Imp(q,Not c));;
