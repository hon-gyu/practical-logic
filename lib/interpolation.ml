open Lib
open Formulas
open Prop
open Defcnf
open Fol
open Skolem
open Herbrand
open Equal
open Order
open Eqelim

(* Warnings the book's style trips in this file; the rest of the
   library compiles with them on.  See lib/dune. *)
[@@@warning "-8"]

(* ========================================================================= *)
(* Implementation/proof of the Craig-Robinson interpolation theorem.         *)
(*                                                                           *)
(* This is based on the proof in Kreisel & Krivine, which works very nicely  *)
(* in our context.                                                           *)
(*                                                                           *)
(* Copyright (c) 2003-2007, John Harrison. (See "LICENSE.txt" for details.)  *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Interpolation for propositional logic.                                    *)
(* ------------------------------------------------------------------------- *)

let pinterpolate p q =
  let orify a r = Or(psubst(a|=>False) r,psubst(a|=>True) r) in
  psimplify(itlist orify (subtract (atoms p) (atoms q)) p);;

(* ------------------------------------------------------------------------- *)
(* Relation-symbol interpolation for universal closed formulas.              *)
(* ------------------------------------------------------------------------- *)

let urinterpolate p q =
  let fm = specialize(prenex(And(p,q))) in
  let fvs = fv fm and consts,funcs = herbfuns fm in
  let cntms = map (fun (c,_) -> Fn(c,[])) consts in
  let tups = dp_refine_loop (simpcnf fm) cntms funcs fvs 0 [] [] [] in
  let fmis = map (fun tup -> subst (fpf fvs tup) fm) tups in
  let ps,qs = unzip (map (fun (And(p,q)) -> p,q) fmis) in
  pinterpolate (list_conj(setify ps)) (list_conj(setify qs));;

let%expect_test "eg" =
  let p = prenex
   {%fol|(forall x. R(x,f(x))) /\ (forall x y. S(x,y) <=> R(x,y) \/ R(y,x))|}
  and q = prenex
   {%fol|(forall x y z. S(x,y) /\ S(y,z) ==> T(x,z)) /\ ~T(0,0)|} in
  print_fol_formula
    (p);
  let c = urinterpolate p q in
  print_fol_formula
    (c);
  print_fol_formula
    (meson(Imp(p,c)));
  print_fol_formula
    (meson(Imp(q,Not c)));
  [%expect {| |}]
;;

(* ------------------------------------------------------------------------- *)
(* Pick the topmost terms starting with one of the given function symbols.   *)
(* ------------------------------------------------------------------------- *)

let rec toptermt fns tm =
  match tm with
    Var x -> []
  | Fn(f,args) -> if mem (f,length args) fns then [tm]
                  else itlist (union ** toptermt fns) args [];;

let topterms fns = atom_union
  (fun (R(p,args)) -> itlist (union ** toptermt fns) args []);;

(* ------------------------------------------------------------------------- *)
(* Interpolation for arbitrary universal formulas.                           *)
(* ------------------------------------------------------------------------- *)

let uinterpolate p q =
  let fp = functions p and fq = functions q in
  let rec simpinter tms n c =
    match tms with
      [] -> c
    | (Fn(f,args) as tm)::otms ->
        let v = "v_"^(string_of_int n) in
        let c' = replace (tm |=> Var v) c in
        let c'' = if mem (f,length args) fp
                  then Exists(v,c') else Forall(v,c') in
        simpinter otms (n+1) c'' in
  let c = urinterpolate p q in
  let tts = topterms (union (subtract fp fq) (subtract fq fp)) c in
  let tms = sort (decreasing termsize) tts in
  simpinter tms 1 c;;

(* ------------------------------------------------------------------------- *)
(* The same example now gives a true interpolant.                            *)
(* ------------------------------------------------------------------------- *)

let%expect_test "eg: The same example now gives a true interpolant" =
  let c = uinterpolate p q in
  print_fol_formula
    (c);
  print_fol_formula
    (meson(Imp(p,c)));
  print_fol_formula
    (meson(Imp(q,Not c)));
  [%expect {| |}]
;;


(* ------------------------------------------------------------------------- *)
(* Now lift to arbitrary formulas with no common free variables.             *)
(* ------------------------------------------------------------------------- *)

let cinterpolate p q =
  let fm = nnf(And(p,q)) in
  let efm = itlist mk_exists (fv fm) fm
  and fns = map fst (functions fm) in
  let And(p',q'),_ = skolem efm fns in
  uinterpolate p' q';;

(* ------------------------------------------------------------------------- *)
(* Now to completely arbitrary formulas.                                     *)
(* ------------------------------------------------------------------------- *)

let interpolate p q =
  let vs = map (fun v -> Var v) (intersect (fv p) (fv q))
  and fns = functions (And(p,q)) in
  let n = itlist (max_varindex "c_" ** fst) fns (Int 0) +/ Int 1 in
  let cs = map (fun i -> Fn("c_"^(string_of_num i),[]))
               (n---(n+/Int(length vs-1))) in
  let fn_vc = fpf vs cs and fn_cv = fpf cs vs in
  let p' = replace fn_vc p and q' = replace fn_vc q in
  replace fn_cv (cinterpolate p' q');;

let%expect_test "eg" =
  let p =
   {%fol|(forall x. exists y. R(x,y)) /\
     (forall x y. S(v,x,y) <=> R(x,y) \/ R(y,x))|}
  and q =
   {%fol|(forall x y z. S(v,x,y) /\ S(v,y,z) ==> T(x,z)) /\
     (exists u. ~T(u,u))|} in
  print_fol_formula
    (p);
  let c = interpolate p q in
  print_fol_formula
    (c);
  print_fol_formula
    (meson(Imp(p,c)));
  print_fol_formula
    (meson(Imp(q,Not c)));
  [%expect {| |}]
;;


(* ------------------------------------------------------------------------- *)
(* Lift to logic with equality.                                              *)
(* ------------------------------------------------------------------------- *)

let einterpolate p q =
  let p' = equalitize p and q' = equalitize q in
  let p'' = if p' = p then p else And(fst(dest_imp p'),p)
  and q'' = if q' = q then q else And(fst(dest_imp q'),q) in
  interpolate p'' q'';;

(* ------------------------------------------------------------------------- *)
(* More examples, not in the text.                                           *)
(* ------------------------------------------------------------------------- *)

let%expect_test "eg: More examples, not in the text" =
  let p = {%fol|(p ==> q /\ r)|}
  and q = {%fol|~((q ==> p) ==> s ==> (p <=> q))|} in
  print_fol_formula
    (p);
  let c = interpolate p q in
  print_fol_formula
    (c);
  print_fol_formula
    (tautology(Imp(And(p,q),False)));
  print_fol_formula
    (tautology(Imp(p,c)));
  print_fol_formula
    (tautology(Imp(q,Not c)));
  (* ------------------------------------------------------------------------- *)
  (* A more interesting example.                                               *)
  (* ------------------------------------------------------------------------- *)
  let p = {%fol|(forall x. exists y. R(x,y)) /\
            (forall x y. S(x,y) <=> R(x,y) \/ R(y,x))|}
  and q = {%fol|(forall x y z. S(x,y) /\ S(y,z) ==> T(x,z)) /\ ~T(u,u)|} in
  print_fol_formula
    (p);
  print_fol_formula
    (meson(Imp(And(p,q),False)));
  let c = interpolate p q in
  print_fol_formula
    (c);
  print_fol_formula
    (meson(Imp(p,c)));
  print_fol_formula
    (meson(Imp(q,Not c)));
  (* ------------------------------------------------------------------------- *)
  (* A variant where u is free in both parts.                                  *)
  (* ------------------------------------------------------------------------- *)
  let p = {%fol|(forall x. exists y. R(x,y)) /\
            (forall x y. S(x,y) <=> R(x,y) \/ R(y,x)) /\
            (forall v. R(u,v) ==> Q(v,u))|}
  and q = {%fol|(forall x y z. S(x,y) /\ S(y,z) ==> T(x,z)) /\ ~T(u,u)|} in
  print_fol_formula
    (p);
  print_fol_formula
    (meson(Imp(And(p,q),False)));
  let c = interpolate p q in
  print_fol_formula
    (c);
  print_fol_formula
    (meson(Imp(p,c)));
  print_fol_formula
    (meson(Imp(q,Not c)));
  (* ------------------------------------------------------------------------- *)
  (* Way of generating examples quite easily (see K&K exercises).              *)
  (* ------------------------------------------------------------------------- *)
  let test_interp fm =
    let p = generalize(skolemize fm)
    and q = generalize(skolemize(Not fm)) in
    let c = interpolate p q in
    meson(Imp(And(p,q),False)); meson(Imp(p,c)); meson(Imp(q,Not c)); c in
  print_fol_formula
    (test_interp {%fol|forall x. P(x) ==> exists y. forall z. P(z) ==> Q(y)|});
  print_fol_formula
    (test_interp {%fol|forall y. exists y. forall z. exists a.
                    P(a,x,y,z) ==> P(x,y,z,a)|});
  (* ------------------------------------------------------------------------- *)
  (* Hintikka's examples.                                                      *)
  (* ------------------------------------------------------------------------- *)
  let p = {%fol|forall x. L(x,b)|}
  and q = {%fol|(forall y. L(b,y) ==> m = y) /\ ~(m = b)|} in
  print_fol_formula
    (p);
  let c = einterpolate p q in
  print_fol_formula
    (c);
  print_fol_formula
    (meson(Imp(p,c)));
  print_fol_formula
    (meson(Imp(q,Not c)));
  let p =
   {%fol|(forall x. A(x) /\ C(x) ==> B(x)) /\ (forall x. D(x) \/ ~D(x) ==> C(x))|}
  and q =
   {%fol|~(forall x. E(x) ==> A(x) ==> B(x))|} in
  print_fol_formula
    (p);
  let c = interpolate p q in
  print_fol_formula
    (c);
  print_fol_formula
    (meson(Imp(p,c)));
  print_fol_formula
    (meson(Imp(q,Not c)));
  [%expect {| |}]
;;
