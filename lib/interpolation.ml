open Lib
open Formulas
open Prop
open Defcnf
open Fol
open Meson
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

(* Kept at top level: the examples below reuse these, as the toplevel did. *)
let p = prenex
 {%fol|(forall x. R(x,f(x))) /\ (forall x y. S(x,y) <=> R(x,y) \/ R(y,x))|}
and q = prenex
 {%fol|(forall x y z. S(x,y) /\ S(y,z) ==> T(x,z)) /\ ~T(0,0)|};;

let%expect_test "eg" =
  print_fol_formula
    (p);
  let c = urinterpolate p q in
  print_fol_formula
    (c);
  print_list print_int
    (meson(Imp(p,c)));
  print_list print_int
    (meson(Imp(q,Not c)));
  [%expect {|
    <<forall x y. R(x,f(x)) /\ (S(x,y) <=> R(x,y) \/ R(y,x))>>0 ground instances tried; 0 items in list
    0 ground instances tried; 0 items in list
    1 ground instances tried; 5 items in list
    1 ground instances tried; 5 items in list
    2 ground instances tried; 6 items in list
    3 ground instances tried; 10 items in list
    <<S(0,f(0)) /\ S(f(0),0) \/ S(0,f(0)) /\ S(f(0),0)>>Searching with depth limit 0Searching with depth limit 1Searching with depth limit 2
    Searching with depth limit 0Searching with depth limit 1Searching with depth limit 2
    [2; 2]Searching with depth limit 0Searching with depth limit 1Searching with depth limit 2Searching with depth limit 3
    [3]
    |}]
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
  print_list print_int
    (meson(Imp(p,c)));
  print_list print_int
    (meson(Imp(q,Not c)));
  [%expect {|
    0 ground instances tried; 0 items in list
    0 ground instances tried; 0 items in list
    1 ground instances tried; 5 items in list
    1 ground instances tried; 5 items in list
    2 ground instances tried; 6 items in list
    3 ground instances tried; 10 items in list
    <<forall v_2.
        exists v_1. S(v_2,v_1) /\ S(v_1,v_2) \/ S(v_2,v_1) /\ S(v_1,v_2)>>Searching with depth limit 0Searching with depth limit 1Searching with depth limit 2Searching with depth limit 3Searching with depth limit 4
    [4]Searching with depth limit 0Searching with depth limit 1Searching with depth limit 2Searching with depth limit 3
    [3]
    |}]
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
  print_list print_int
    (meson(Imp(p,c)));
  print_list print_int
    (meson(Imp(q,Not c)));
  [%expect {|
    <<(forall x. exists y. R(x,y)) /\ (forall x y. S(v,x,y) <=> R(x,y) \/ R(y,x))>>0 ground instances tried; 0 items in list
    0 ground instances tried; 0 items in list
    1 ground instances tried; 5 items in list
    2 ground instances tried; 6 items in list
    3 ground instances tried; 10 items in list
    4 ground instances tried; 11 items in list
    5 ground instances tried; 16 items in list
    6 ground instances tried; 17 items in list
    7 ground instances tried; 20 items in list
    8 ground instances tried; 21 items in list
    8 ground instances tried; 21 items in list
    9 ground instances tried; 22 items in list
    10 ground instances tried; 23 items in list
    11 ground instances tried; 24 items in list
    12 ground instances tried; 25 items in list
    13 ground instances tried; 29 items in list
    14 ground instances tried; 30 items in list
    15 ground instances tried; 34 items in list
    16 ground instances tried; 35 items in list
    17 ground instances tried; 36 items in list
    18 ground instances tried; 37 items in list
    19 ground instances tried; 38 items in list
    20 ground instances tried; 39 items in list
    21 ground instances tried; 43 items in list
    22 ground instances tried; 44 items in list
    23 ground instances tried; 48 items in list
    24 ground instances tried; 49 items in list
    25 ground instances tried; 54 items in list
    26 ground instances tried; 55 items in list
    27 ground instances tried; 59 items in list
    28 ground instances tried; 60 items in list
    29 ground instances tried; 65 items in list
    30 ground instances tried; 66 items in list
    <<forall v_2.
        exists v_1. S(v,v_2,v_1) /\ S(v,v_1,v_2) \/ S(v,v_2,v_1) /\ S(v,v_1,v_2)>>Searching with depth limit 0Searching with depth limit 1Searching with depth limit 2Searching with depth limit 3Searching with depth limit 4
    [4]Searching with depth limit 0Searching with depth limit 1Searching with depth limit 2Searching with depth limit 3
    [3]
    |}]
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
  print_bool
    (tautology(Imp(And(p,q),False)));
  print_bool
    (tautology(Imp(p,c)));
  print_bool
    (tautology(Imp(q,Not c)));
  (* ------------------------------------------------------------------------- *)
  (* A more interesting example.                                               *)
  (* ------------------------------------------------------------------------- *)
  let p = {%fol|(forall x. exists y. R(x,y)) /\
            (forall x y. S(x,y) <=> R(x,y) \/ R(y,x))|}
  and q = {%fol|(forall x y z. S(x,y) /\ S(y,z) ==> T(x,z)) /\ ~T(u,u)|} in
  print_fol_formula
    (p);
  print_list print_int
    (meson(Imp(And(p,q),False)));
  let c = interpolate p q in
  print_fol_formula
    (c);
  print_list print_int
    (meson(Imp(p,c)));
  print_list print_int
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
  print_list print_int
    (meson(Imp(And(p,q),False)));
  let c = interpolate p q in
  print_fol_formula
    (c);
  print_list print_int
    (meson(Imp(p,c)));
  print_list print_int
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
  print_list print_int
    (meson(Imp(p,c)));
  print_list print_int
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
  print_list print_int
    (meson(Imp(p,c)));
  print_list print_int
    (meson(Imp(q,Not c)));
  [%expect {|
    <<p ==> q /\ r>>0 ground instances tried; 0 items in list
    0 ground instances tried; 0 items in list
    <<~p \/ ~p \/ q>>truetruetrue<<(forall x. exists y. R(x,y)) /\
                                   (forall x y. S(x,y) <=> R(x,y) \/ R(y,x))>>Searching with depth limit 0Searching with depth limit 1Searching with depth limit 2Searching with depth limit 3Searching with depth limit 4Searching with depth limit 5
    [5]0 ground instances tried; 0 items in list
    0 ground instances tried; 0 items in list
    1 ground instances tried; 5 items in list
    1 ground instances tried; 5 items in list
    2 ground instances tried; 6 items in list
    3 ground instances tried; 10 items in list
    <<forall v_2.
        exists v_1. S(v_2,v_1) /\ S(v_1,v_2) \/ S(v_2,v_1) /\ S(v_1,v_2)>>Searching with depth limit 0Searching with depth limit 1Searching with depth limit 2Searching with depth limit 3Searching with depth limit 4
    [4]Searching with depth limit 0Searching with depth limit 1Searching with depth limit 2Searching with depth limit 3
    [3]<<(forall x. exists y. R(x,y)) /\
         (forall x y. S(x,y) <=> R(x,y) \/ R(y,x)) /\
         (forall v. R(u,v) ==> Q(v,u))>>Searching with depth limit 0Searching with depth limit 1Searching with depth limit 2Searching with depth limit 3Searching with depth limit 4Searching with depth limit 5
    [5]0 ground instances tried; 0 items in list
    0 ground instances tried; 0 items in list
    1 ground instances tried; 6 items in list
    1 ground instances tried; 6 items in list
    2 ground instances tried; 7 items in list
    3 ground instances tried; 11 items in list
    <<exists v_1.
        (S(u,v_1) /\ S(v_1,u) \/ S(u,v_1) /\ S(v_1,u)) \/
        (S(u,v_1) /\ S(v_1,u) \/ S(u,v_1) /\ S(v_1,u)) \/
        S(u,v_1) /\ S(v_1,u) \/ S(u,v_1) /\ S(v_1,u)>>Searching with depth limit 0Searching with depth limit 1Searching with depth limit 2Searching with depth limit 3Searching with depth limit 4
    [4]Searching with depth limit 0Searching with depth limit 1Searching with depth limit 2Searching with depth limit 3
    [3]0 ground instances tried; 0 items in list
    0 ground instances tried; 0 items in list
    1 ground instances tried; 4 items in list
    2 ground instances tried; 5 items in list
    Searching with depth limit 0Searching with depth limit 1Searching with depth limit 2Searching with depth limit 3
    Searching with depth limit 0Searching with depth limit 1Searching with depth limit 2Searching with depth limit 3
    Searching with depth limit 0Searching with depth limit 1Searching with depth limit 2
    <<forall v_2.
        exists v_1.
          (~P(v_2) \/ ~P(v_2) \/ Q(v_1)) \/
          (~P(v_2) \/ ~P(v_2) \/ Q(v_1)) /\ (~P(v_2) \/ Q(v_1))>>0 ground instances tried; 0 items in list
    0 ground instances tried; 0 items in list
    1 ground instances tried; 3 items in list
    1 ground instances tried; 3 items in list
    2 ground instances tried; 6 items in list
    3 ground instances tried; 9 items in list
    4 ground instances tried; 12 items in list
    5 ground instances tried; 14 items in list
    6 ground instances tried; 16 items in list
    7 ground instances tried; 18 items in list
    8 ground instances tried; 21 items in list
    9 ground instances tried; 24 items in list
    10 ground instances tried; 27 items in list
    10 ground instances tried; 27 items in list
    11 ground instances tried; 30 items in list
    12 ground instances tried; 33 items in list
    13 ground instances tried; 36 items in list
    14 ground instances tried; 39 items in list
    15 ground instances tried; 42 items in list
    16 ground instances tried; 45 items in list
    17 ground instances tried; 48 items in list
    18 ground instances tried; 51 items in list
    19 ground instances tried; 54 items in list
    20 ground instances tried; 57 items in list
    21 ground instances tried; 60 items in list
    22 ground instances tried; 63 items in list
    23 ground instances tried; 66 items in list
    24 ground instances tried; 69 items in list
    25 ground instances tried; 72 items in list
    26 ground instances tried; 74 items in list
    27 ground instances tried; 76 items in list
    28 ground instances tried; 78 items in list
    29 ground instances tried; 80 items in list
    30 ground instances tried; 82 items in list
    31 ground instances tried; 84 items in list
    32 ground instances tried; 86 items in list
    33 ground instances tried; 88 items in list
    34 ground instances tried; 90 items in list
    35 ground instances tried; 92 items in list
    36 ground instances tried; 94 items in list
    37 ground instances tried; 96 items in list
    38 ground instances tried; 98 items in list
    39 ground instances tried; 100 items in list
    40 ground instances tried; 102 items in list
    41 ground instances tried; 104 items in list
    42 ground instances tried; 106 items in list
    43 ground instances tried; 108 items in list
    44 ground instances tried; 110 items in list
    45 ground instances tried; 112 items in list
    46 ground instances tried; 114 items in list
    47 ground instances tried; 116 items in list
    48 ground instances tried; 118 items in list
    49 ground instances tried; 120 items in list
    50 ground instances tried; 123 items in list
    51 ground instances tried; 126 items in list
    52 ground instances tried; 129 items in list
    53 ground instances tried; 131 items in list
    54 ground instances tried; 133 items in list
    55 ground instances tried; 135 items in list
    56 ground instances tried; 138 items in list
    57 ground instances tried; 141 items in list
    58 ground instances tried; 144 items in list
    59 ground instances tried; 146 items in list
    60 ground instances tried; 148 items in list
    61 ground instances tried; 150 items in list
    62 ground instances tried; 153 items in list
    63 ground instances tried; 156 items in list
    64 ground instances tried; 159 items in list
    65 ground instances tried; 161 items in list
    66 ground instances tried; 163 items in list
    67 ground instances tried; 165 items in list
    68 ground instances tried; 168 items in list
    69 ground instances tried; 171 items in list
    70 ground instances tried; 174 items in list
    71 ground instances tried; 177 items in list
    72 ground instances tried; 180 items in list
    73 ground instances tried; 183 items in list
    74 ground instances tried; 186 items in list
    75 ground instances tried; 189 items in list
    76 ground instances tried; 192 items in list
    77 ground instances tried; 195 items in list
    78 ground instances tried; 198 items in list
    Searching with depth limit 0Searching with depth limit 1
    Searching with depth limit 0Searching with depth limit 1
    <<true>><<forall x. L(x,b)>>0 ground instances tried; 0 items in list
    0 ground instances tried; 0 items in list
    <<L(b,b)>>Searching with depth limit 0Searching with depth limit 1
    [1]Searching with depth limit 0Searching with depth limit 1Searching with depth limit 2
    [2]<<(forall x. A(x) /\ C(x) ==> B(x)) /\ (forall x. D(x) \/ ~D(x) ==> C(x))>>0 ground instances tried; 0 items in list
    0 ground instances tried; 0 items in list
    <<forall v_1. (~A(v_1) \/ B(v_1)) \/ ~A(v_1) \/ B(v_1)>>Searching with depth limit 0Searching with depth limit 1Searching with depth limit 2Searching with depth limit 3Searching with depth limit 4Searching with depth limit 5
    [5]Searching with depth limit 0Searching with depth limit 1Searching with depth limit 2
    [2]
    |}]
;;
