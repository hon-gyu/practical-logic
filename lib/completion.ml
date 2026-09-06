open Lib
open Formulas
open Fol
open Meson
open Unif
open Equal
open Rewrite
open Order
open Skolem

(* Warnings the book's style trips in this file; the rest of the
   library compiles with them on.  See lib/dune. *)
[@@@warning "-8"]

(* ========================================================================= *)
(* Knuth-Bendix completion.                                                  *)
(*                                                                           *)
(* Copyright (c) 2003-2007, John Harrison. (See "LICENSE.txt" for details.)  *)
(* ========================================================================= *)

let renamepair (fm1,fm2) =
  let fvs1 = fv fm1 and fvs2 = fv fm2 in
  let nms1,nms2 = chop_list(length fvs1)
                           (map (fun n -> Var("x"^string_of_int n))
                                (0--(length fvs1 + length fvs2 - 1))) in
  subst (fpf fvs1 nms1) fm1,subst (fpf fvs2 nms2) fm2;;

(* ------------------------------------------------------------------------- *)
(* Rewrite (using unification) with l = r inside tm to give a critical pair. *)
(* ------------------------------------------------------------------------- *)

let rec listcases fn rfn lis acc =
  match lis with
    [] -> acc
  | h::t -> fn h (fun i h' -> rfn i (h'::t)) @
            listcases fn (fun i t' -> rfn i (h::t')) t acc;;

let rec overlaps (l,r) tm rfn =
  match tm with
    Fn(f,args) ->
        listcases (overlaps (l,r)) (fun i a -> rfn i (Fn(f,a))) args
                  (try [rfn (fullunify [l,tm]) r] with Failure _ -> [])
  | Var x -> [];;

(* ------------------------------------------------------------------------- *)
(* Generate all critical pairs between two equations.                        *)
(* ------------------------------------------------------------------------- *)

let crit1 (Atom(R("=",[l1;r1]))) (Atom(R("=",[l2;r2]))) =
  overlaps (l1,r1) l2 (fun i t -> subst i (mk_eq t r2));;

let critical_pairs fma fmb =
  let fm1,fm2 = renamepair (fma,fmb) in
  if fma = fmb then crit1 fm1 fm2
  else union (crit1 fm1 fm2) (crit1 fm2 fm1);;

(* ------------------------------------------------------------------------- *)
(* Simple example.                                                           *)
(* ------------------------------------------------------------------------- *)


let%expect_test "eg: Simple example" =
  print_list print_fol_formula
    (let eq = {%fol|f(f(x)) = g(x)|} in critical_pairs eq eq);
  [%expect {| [<<f(g(x0)) = g(f(x0))>>; <<g(x1) = g(x1)>>] |}]
;;

(* ------------------------------------------------------------------------- *)
(* Orienting an equation.                                                    *)
(* ------------------------------------------------------------------------- *)

let normalize_and_orient ord eqs (Atom(R("=",[s;t]))) =
  let s' = rewrite eqs s and t' = rewrite eqs t in
  if ord s' t' then (s',t') else if ord t' s' then (t',s')
  else failwith "Can't orient equation";;

(* ------------------------------------------------------------------------- *)
(* Status report so the user doesn't get too bored.                          *)
(* ------------------------------------------------------------------------- *)

let status(eqs,def,crs) eqs0 =
  if eqs = eqs0 && (length crs) mod 1000 <> 0 then () else
  (print_string(string_of_int(length eqs)^" equations and "^
                string_of_int(length crs)^" pending critical pairs + "^
                string_of_int(length def)^" deferred");
   print_newline());;

(* ------------------------------------------------------------------------- *)
(* Completion main loop (deferring non-orientable equations).                *)
(* ------------------------------------------------------------------------- *)

let rec complete ord (eqs,def,crits) =
  match crits with
    eq::ocrits ->
        let trip =
          try let (s',t') = normalize_and_orient ord eqs eq in
              if s' = t' then (eqs,def,ocrits) else
              let eq' = Atom(R("=",[s';t'])) in
              let eqs' = eq'::eqs in
              eqs',def,
              ocrits @ itlist ((@) ** critical_pairs eq') eqs' []
          with Failure _ -> (eqs,eq::def,ocrits) in
        status trip eqs; complete ord trip
  | _ -> if def = [] then eqs else
         let e = find (can (normalize_and_orient ord eqs)) def in
         complete ord (eqs,subtract def [e],[e]);;

(* ------------------------------------------------------------------------- *)
(* A simple "manual" example, before considering packaging and refinements.  *)
(* ------------------------------------------------------------------------- *)

let%expect_test "eg: A simple 'manual' example, before considering packaging and refinements" =
  let eqs =
    [{%fol|1 * x = x|}; {%fol|i(x) * x = 1|}; {%fol|(x * y) * z = x * y * z|}] in
  print_list print_fol_formula
    (eqs);
  let ord = lpo_ge (weight ["1"; "*"; "i"]) in
  ignore
    (ord);
  let eqs' = complete ord
    (eqs,[],unions(allpairs critical_pairs eqs eqs)) in
  print_list print_fol_formula
    (eqs');
  printert
    (rewrite eqs' {%tm|i(x * i(x)) * (i(i((y * z) * u) * y) * i(u))|});
  [%expect {|
    [<<1 * x = x>>; <<i(x) * x = 1>>; <<(x * y) * z = x * y * z>>]4 equations and 8 pending critical pairs + 0 deferred
    5 equations and 12 pending critical pairs + 0 deferred
    6 equations and 16 pending critical pairs + 0 deferred
    7 equations and 27 pending critical pairs + 0 deferred
    8 equations and 51 pending critical pairs + 0 deferred
    9 equations and 70 pending critical pairs + 0 deferred
    10 equations and 81 pending critical pairs + 0 deferred
    11 equations and 78 pending critical pairs + 0 deferred
    12 equations and 85 pending critical pairs + 0 deferred
    13 equations and 114 pending critical pairs + 0 deferred
    14 equations and 151 pending critical pairs + 0 deferred
    15 equations and 180 pending critical pairs + 0 deferred
    16 equations and 247 pending critical pairs + 0 deferred
    17 equations and 298 pending critical pairs + 0 deferred
    18 equations and 356 pending critical pairs + 0 deferred
    19 equations and 404 pending critical pairs + 0 deferred
    20 equations and 485 pending critical pairs + 0 deferred
    21 equations and 530 pending critical pairs + 0 deferred
    22 equations and 583 pending critical pairs + 0 deferred
    23 equations and 642 pending critical pairs + 0 deferred
    24 equations and 730 pending critical pairs + 0 deferred
    25 equations and 779 pending critical pairs + 0 deferred
    26 equations and 794 pending critical pairs + 0 deferred
    27 equations and 819 pending critical pairs + 1 deferred
    28 equations and 918 pending critical pairs + 1 deferred
    29 equations and 901 pending critical pairs + 1 deferred
    30 equations and 1005 pending critical pairs + 1 deferred
    31 equations and 1086 pending critical pairs + 1 deferred
    32 equations and 1155 pending critical pairs + 1 deferred
    32 equations and 1000 pending critical pairs + 1 deferred
    32 equations and 0 pending critical pairs + 1 deferred
    32 equations and 0 pending critical pairs + 0 deferred
    [<<i(x4 * x5) = i(x5) * i(x4)>>; <<x1 * i(x5 * x1) = i(x5)>>; <<i(x4) * x1 *
                                                                    i(x3 * x1) =
                                                                    i(x4) * i(
                                                                    x3)>>;
    <<x1 * i(i(x4) * i(x3) * x1) = x3 * x4>>; <<i(x3 * x5) * x0 = i(x5) * i(
                                                x3) * x0>>; <<i(x4 * x5 * x6 * x3) *
                                                              x0 = i(x3) *
                                                              i(x4 * x5 * x6) *
                                                              x0>>; <<i(x0 *
                                                                        i(
                                                                        x1)) =
                                                                      x1 * i(
                                                                      x0)>>;
    <<i(i(x2 * x1) * x2) = x1>>; <<i(i(x4) * x2) * x0 = i(x2) * x4 * x0>>;
    <<x1 * i(x2 * x1) * x2 = 1>>; <<x1 * i(i(x4 * x5) * x1) * x3 = x4 * x5 * x3>>;
    <<i(x3 * i(x1 * x2)) = x1 * x2 * i(x3)>>; <<i(i(x3 * i(x1 * x2)) * i(x5 * x6)) *
                                                x1 * x2 * x0 = x5 * x6 * x3 * x0>>;
    <<x1 * x2 * i(x1 * x2) = 1>>; <<x2 * x3 * i(x2 * x3) * x1 = x1>>; <<i(
                                                                        x3 * x4) *
                                                                        x3 * x1 =
                                                                        i(
                                                                        x4) * x1>>;
    <<i(x1 * x3 * x4) * x1 * x3 * x4 * x0 = x0>>; <<i(x1 * i(x3)) * x1 * x4 =
                                                    x3 * x4>>; <<i(i(x5 * x2) *
                                                                   x5) *
                                                                 x0 = x2 * x0>>;
    <<i(x4 * i(x1 * x2)) * x4 * x0 = x1 * x2 * x0>>; <<i(i(x1)) = x1>>; <<
                                                                        i(
                                                                        1) = 1>>;
    <<x0 * i(x0) = 1>>; <<x0 * i(x0) * x3 = x3>>; <<i(x2 * x3) * x2 * x3 * x1 =
                                                    x1>>; <<x1 * 1 = x1>>;
    <<i(1) * x1 = x1>>; <<i(i(x0)) * x1 = x0 * x1>>; <<i(x1) * x1 * x2 = x2>>;
    <<1 * x = x>>; <<i(x) * x = 1>>; <<(x * y) * z = x * y * z>>]<<|z|>>
    |}]
;;


(* ------------------------------------------------------------------------- *)
(* Interreduction.                                                           *)
(* ------------------------------------------------------------------------- *)

let rec interreduce dun eqs =
  match eqs with
    (Atom(R("=",[l;r])))::oeqs ->
        let dun' = if rewrite (dun @ oeqs) l <> l then dun
                   else mk_eq l (rewrite (dun @ eqs) r)::dun in
        interreduce dun' oeqs
  | [] -> rev dun;;

(* ------------------------------------------------------------------------- *)
(* This does indeed help a lot.                                              *)
(* ------------------------------------------------------------------------- *)

let%expect_test "eg: This does indeed help a lot" =
  let eqs =
    [{%fol|1 * x = x|}; {%fol|i(x) * x = 1|}; {%fol|(x * y) * z = x * y * z|}] in
  let ord = lpo_ge (weight ["1"; "*"; "i"]) in
  let eqs' = complete ord
    (eqs,[],unions(allpairs critical_pairs eqs eqs)) in
  print_list print_fol_formula
    (interreduce [] eqs');
  [%expect {|
    4 equations and 8 pending critical pairs + 0 deferred
    5 equations and 12 pending critical pairs + 0 deferred
    6 equations and 16 pending critical pairs + 0 deferred
    7 equations and 27 pending critical pairs + 0 deferred
    8 equations and 51 pending critical pairs + 0 deferred
    9 equations and 70 pending critical pairs + 0 deferred
    10 equations and 81 pending critical pairs + 0 deferred
    11 equations and 78 pending critical pairs + 0 deferred
    12 equations and 85 pending critical pairs + 0 deferred
    13 equations and 114 pending critical pairs + 0 deferred
    14 equations and 151 pending critical pairs + 0 deferred
    15 equations and 180 pending critical pairs + 0 deferred
    16 equations and 247 pending critical pairs + 0 deferred
    17 equations and 298 pending critical pairs + 0 deferred
    18 equations and 356 pending critical pairs + 0 deferred
    19 equations and 404 pending critical pairs + 0 deferred
    20 equations and 485 pending critical pairs + 0 deferred
    21 equations and 530 pending critical pairs + 0 deferred
    22 equations and 583 pending critical pairs + 0 deferred
    23 equations and 642 pending critical pairs + 0 deferred
    24 equations and 730 pending critical pairs + 0 deferred
    25 equations and 779 pending critical pairs + 0 deferred
    26 equations and 794 pending critical pairs + 0 deferred
    27 equations and 819 pending critical pairs + 1 deferred
    28 equations and 918 pending critical pairs + 1 deferred
    29 equations and 901 pending critical pairs + 1 deferred
    30 equations and 1005 pending critical pairs + 1 deferred
    31 equations and 1086 pending critical pairs + 1 deferred
    32 equations and 1155 pending critical pairs + 1 deferred
    32 equations and 1000 pending critical pairs + 1 deferred
    32 equations and 0 pending critical pairs + 1 deferred
    32 equations and 0 pending critical pairs + 0 deferred
    [<<i(x4 * x5) = i(x5) * i(x4)>>; <<i(i(x1)) = x1>>; <<i(1) = 1>>; <<x0 *
                                                                        i(
                                                                        x0) = 1>>;
    <<x0 * i(x0) * x3 = x3>>; <<x1 * 1 = x1>>; <<i(x1) * x1 * x2 = x2>>;
    <<1 * x = x>>; <<i(x) * x = 1>>; <<(x * y) * z = x * y * z>>]
    |}]
;;


(* ------------------------------------------------------------------------- *)
(* Overall function with post-simplification (but not dynamically).          *)
(* ------------------------------------------------------------------------- *)

let complete_and_simplify wts eqs =
  let ord = lpo_ge (weight wts) in
  let eqs' = map (fun e -> let l,r = normalize_and_orient ord [] e in
                           mk_eq l r) eqs in
  (interreduce [] ** complete ord)
  (eqs',[],unions(allpairs critical_pairs eqs' eqs'));;

(* ------------------------------------------------------------------------- *)
(* Inverse property (K&B example 4).                                         *)
(* ------------------------------------------------------------------------- *)

let%expect_test "eg: Inverse property (K&B example 4)" =
  print_list print_fol_formula
    (complete_and_simplify ["1"; "*"; "i"]
      [{%fol|i(a) * (a * b) = b|}]);
  (* ------------------------------------------------------------------------- *)
  (* Auxiliary result used to justify extension of language for cancellation.  *)
  (* ------------------------------------------------------------------------- *)
  print_list print_int
    ((meson ** equalitize)
     {%fol|(forall x y z. x * y = x * z ==> y = z) <=>
       (forall x z. exists w. forall y. z = x * y ==> w = y)|});
  print_fol_formula
    (skolemize {%fol|forall x z. exists w. forall y. z = x * y ==> w = y|});
  [%expect {|
    2 equations and 4 pending critical pairs + 0 deferred
    3 equations and 9 pending critical pairs + 0 deferred
    3 equations and 0 pending critical pairs + 0 deferred
    [<<x0 * i(x0) * x3 = x3>>; <<i(i(x0)) * x1 = x0 * x1>>; <<i(a) * a * b = b>>]Searching with depth limit 0Searching with depth limit 1Searching with depth limit 2Searching with depth limit 3Searching with depth limit 4Searching with depth limit 5
    Searching with depth limit 0Searching with depth limit 1Searching with depth limit 2Searching with depth limit 3Searching with depth limit 4
    [5; 4]<<~z = x * y \/ f_w(x,z) = y>>
    |}]
;;


(* ------------------------------------------------------------------------- *)
(* The commutativity example (of course it fails...).                        *)
(* ------------------------------------------------------------------------- *)

(*******************

#trace complete;;

complete_and_simplify ["1"; "*"; "i"]
 [{%fol|(x * y) * z = x * (y * z)|};
  {%fol|1 * x = x|}; {%fol|x * 1 = x|}; {%fol|x * x = 1|}];;

 ********************)

(* ------------------------------------------------------------------------- *)
(* Central groupoids (K&B example 6).                                        *)
(* ------------------------------------------------------------------------- *)

let%expect_test "eg: Central groupoids (K&B example 6)" =
  let eqs =  [{%fol|(a * b) * (b * c) = b|}] in
  print_list print_fol_formula
    (eqs);
  print_list print_fol_formula
    (complete_and_simplify ["*"] eqs);
  (* ------------------------------------------------------------------------- *)
  (* (l,r)-systems (K&B example 12).                                           *)
  (* ------------------------------------------------------------------------- *)

  (******** This works, but takes a long time

  let eqs =
   [{%fol|(x * y) * z = x * y * z|}; {%fol|1 * x = x|}; {%fol|x * i(x) = 1|}];;

  complete_and_simplify ["1"; "*"; "i"] eqs;;

   ***********)

  (* ------------------------------------------------------------------------- *)
  (* Auxiliary result used to justify extension for example 9.                 *)
  (* ------------------------------------------------------------------------- *)
  print_list print_int
    ((meson ** equalitize)
     {%fol|(forall x y z. x * y = x * z ==> y = z) <=>
       (forall x z. exists w. forall y. z = x * y ==> w = y)|});
  print_fol_formula
    (skolemize {%fol|forall x z. exists w. forall y. z = x * y ==> w = y|});
  let eqs =
    [{%fol|f(a,a*b) = b|}; {%fol|g(a*b,b) = a|}; {%fol|1 * a = a|}; {%fol|a * 1 = a|}] in
  print_list print_fol_formula
    (eqs);
  print_list print_fol_formula
    (complete_and_simplify ["1"; "*"; "f"; "g"] eqs);
  (* ------------------------------------------------------------------------- *)
  (* K&B example 7, where we need to divide through.                           *)
  (* ------------------------------------------------------------------------- *)
  let eqs =  [{%fol|f(a,f(b,c,a),d) = c|}] in
  print_list print_fol_formula
    (eqs);
  (*********** Can't orient

  complete_and_simplify ["f"] eqs;;

  *************)
  let eqs =  [{%fol|f(a,f(b,c,a),d) = c|}; {%fol|f(a,b,c) = g(a,b)|};
                       {%fol|g(a,b) = h(b)|}] in
  print_list print_fol_formula
    (eqs);
  print_list print_fol_formula
    (complete_and_simplify ["h"; "g"; "f"] eqs);
  (* ------------------------------------------------------------------------- *)
  (* Other examples not in the book, mostly from K&B                           *)
  (* ------------------------------------------------------------------------- *)

  (************

  (* ------------------------------------------------------------------------- *)
  (* Group theory I (K & B example 1).                                         *)
  (* ------------------------------------------------------------------------- *)

  let eqs =
   [{%fol|1 * x = x|}; {%fol|i(x) * x = 1|}; {%fol|(x * y) * z = x * y * z|}];;

  complete_and_simplify ["1"; "*"; "i"] eqs;;

  (* ------------------------------------------------------------------------- *)
  (* However, with the rules in a different order, things take longer.         *)
  (* At least we don't need to defer any critical pairs...                     *)
  (* ------------------------------------------------------------------------- *)

  let eqs =
   [{%fol|(x * y) * z = x * y * z|}; {%fol|1 * x = x|}; {%fol|i(x) * x = 1|}];;

  complete_and_simplify ["1"; "*"; "i"] eqs;;

  (* ------------------------------------------------------------------------- *)
  (* Example 2: if we orient i(x) * i(y) -> i(x * y), things diverge.          *)
  (* ------------------------------------------------------------------------- *)

  (**************

  let eqs =
   [{%fol|1 * x = x|}; {%fol|i(x) * x = 1|}; {%fol|(x * y) * z = x * y * z|}];;

  complete_and_simplify ["1"; "i"; "*"] eqs;;
   *************)

  (* ------------------------------------------------------------------------- *)
  (* Group theory III, with right inverse and identity (K&B example 3).        *)
  (* ------------------------------------------------------------------------- *)

  let eqs =
   [{%fol|(x * y) * z = x * y * z|}; {%fol|x * 1 = x|}; {%fol|x * i(x) = 1|}];;

  complete_and_simplify ["1"; "*"; "i"] eqs;;

  (* ------------------------------------------------------------------------- *)
  (* Inverse property (K&B example 4).                                         *)
  (* ------------------------------------------------------------------------- *)

  let eqs =  [{%fol|i(a) * (a * b) = b|}];;

  complete_and_simplify ["1"; "*"; "i"] eqs;;

  let eqs =  [{%fol|a * (i(a) * b) = b|}];;

  complete_and_simplify ["1"; "*"; "i"] eqs;;

  (* ------------------------------------------------------------------------- *)
  (* Group theory IV (K&B example 5).                                          *)
  (* ------------------------------------------------------------------------- *)

  let eqs =
   [{%fol|(x * y) * z = x * y * z|};
    {%fol|1 * x = x|}; {%fol|11 * x = x|};
    {%fol|i(x) * x = 1|}; {%fol|j(x) * x = 11|}];;

  complete_and_simplify ["1"; "11"; "*"; "i"; "j"] eqs;;

  (* ------------------------------------------------------------------------- *)
  (* Central groupoids (K&B example 6).                                        *)
  (* ------------------------------------------------------------------------- *)

  let eqs =  [{%fol|(a * b) * (b * c) = b|}];;

  complete_and_simplify ["*"] eqs;;

  (* ------------------------------------------------------------------------- *)
  (* Random axiom (K&B example 7).                                             *)
  (* ------------------------------------------------------------------------- *)

  let eqs =  [{%fol|f(a,f(b,c,a),d) = c|}];;

  (*********** Can't orient

  complete_and_simplify ["f"] eqs;;

  *************)

  let eqs =  [{%fol|f(a,f(b,c,a),d) = c|}; {%fol|f(a,b,c) = g(a,b)|};
                       {%fol|g(a,b) = h(b)|}];;

  complete_and_simplify ["h"; "g"; "f"] eqs;;

  (* ------------------------------------------------------------------------- *)
  (* Another random axiom (K&B example 8).                                     *)
  (* ------------------------------------------------------------------------- *)

  (************* Can't orient

  let eqs =  [{%fol|(a * b) * (c * b * a) = b|}];;

  complete_and_simplify ["*"] eqs;;

   *************)

  (* ------------------------------------------------------------------------- *)
  (* The cancellation law (K&B example 9).                                     *)
  (* ------------------------------------------------------------------------- *)

  let eqs =  [{%fol|f(a,a*b) = b|}; {%fol|g(a*b,b) = a|}];;

  complete_and_simplify ["*"; "f"; "g"] eqs;;

  let eqs =
    [{%fol|f(a,a*b) = b|}; {%fol|g(a*b,b) = a|}; {%fol|1 * a = a|}; {%fol|a * 1 = a|}];;

  complete_and_simplify ["1"; "*"; "f"; "g"] eqs;;

  (**** Just for fun; these aren't tried by Knuth and Bendix

  let eqs =
    [{%fol|(x * y) * z = x * y * z|};
     {%fol|f(a,a*b) = b|}; {%fol|g(a*b,b) = a|}; {%fol|1 * a = a|}; {%fol|a * 1 = a|}];;

  complete_and_simplify ["1"; "*"; "f"; "g"] eqs;;

  let eqs =
    [{%fol|(x * y) * z = x * y * z|};
     {%fol|f(a,a*b) = b|}; {%fol|g(a*b,b) = a|}];;

  complete_and_simplify ["*"; "f"; "g"] eqs;;

  complete_and_simplify ["f"; "g"; "*"] eqs;;

  *********)

  (* ------------------------------------------------------------------------- *)
  (* Loops (K&B example 10).                                                   *)
  (* ------------------------------------------------------------------------- *)

  let eqs =
   [{%fol|a * \(a,b) = b|}; {%fol|/(a,b) * b = a|}; {%fol|1 * a = a|}; {%fol|a * 1 = a|}];;

  complete_and_simplify ["1"; "*"; "\\"; "/"] eqs;;

  let eqs =
   [{%fol|a * \(a,b) = b|}; {%fol|/(a,b) * b = a|}; {%fol|1 * a = a|}; {%fol|a * 1 = a|};
    {%fol|f(a,a*b) = b|}; {%fol|g(a*b,b) = a|}];;

  complete_and_simplify ["1"; "*"; "\\"; "/"; "f"; "g"] eqs;;

  (* ------------------------------------------------------------------------- *)
  (* Another variant of groups (K&B example 11).                               *)
  (* ------------------------------------------------------------------------- *)

  let eqs =
   [{%fol|(x * y) * z = x * y * z|};
    {%fol|1 * 1 = 1|};
    {%fol|a * i(a) = 1|};
    {%fol|f(1,a,b) = a|};
    {%fol|f(a*b,a,b) = g(a*b,b)|}];;

  (******** this is not expected to terminate

  complete_and_simplify ["1"; "g"; "f"; "*"; "i"] eqs;;

  **************)

  (* ------------------------------------------------------------------------- *)
  (* (l,r)-systems (K&B example 12).                                           *)
  (* ------------------------------------------------------------------------- *)

  (******** This works, but takes a long time

  let eqs =
   [{%fol|(x * y) * z = x * y * z|}; {%fol|1 * x = x|}; {%fol|x * i(x) = 1|}];;

  complete_and_simplify ["1"; "*"; "i"] eqs;;

   ***********)

  (* ------------------------------------------------------------------------- *)
  (* (r,l)-systems (K&B example 13).                                           *)
  (* ------------------------------------------------------------------------- *)

  (**** Note that here the simple LPO approach works, whereas K&B need
   **** some additional hacks.
   ****)

  let eqs =
   [{%fol|(x * y) * z = x * y * z|}; {%fol|x * 1 = x|}; {%fol|i(x) * x = 1|}];;

  complete_and_simplify ["1"; "*"; "i"] eqs;;

  (* ------------------------------------------------------------------------- *)
  (* (l,r) systems II (K&B example 14).                                        *)
  (* ------------------------------------------------------------------------- *)

  let eqs =
   [{%fol|(x * y) * z = x * y * z|};
    {%fol|1 * x = x|}; {%fol|11 * x = x|};
    {%fol|x * i(x) = 1|}; {%fol|x * j(x) = 11|}];;

  (******** This seems to be too slow. K&B encounter a similar problem

  complete_and_simplify ["1"; "11"; "*"; "i"; "j"] eqs;;

   ********)

  (* ------------------------------------------------------------------------- *)
  (* (l,r) systems III (K&B example 15).                                       *)
  (* ------------------------------------------------------------------------- *)

  (********** According to KB, this wouldn't be expected to work

  let eqs =
   [{%fol|(x * y) * z = x * y * z|};
    {%fol|1 * x = x|};
    {%fol|prime(a) * a = star(a)|};
    {%fol|star(a) * b = b|}];;

  complete_and_simplify ["1"; "*"; "star"; "prime"] eqs;;

   ************)

  (*********** These seem too slow too. Maybe just a bad ordering?

  let eqs =
   [{%fol|(x * y) * z = x * y * z|};
    {%fol|1 * x = x|};
    {%fol|hash(a) * dollar(a) * a = star(a)|};
    {%fol|star(a) * b = b|};
    {%fol|a * hash(a) = 1|};
    {%fol|a * 1 = hash(hash(a))|};
    {%fol|hash(hash(hash(a))) = hash(a)|}];;

  complete_and_simplify ["1"; "hash"; "star"; "*"; "dollar"] eqs;;

  let eqs =
   [{%fol|(x * y) * z = x * y * z|};
    {%fol|1 * x = x|};
    {%fol|hash(a) * dollar(a) * a = star(a)|};
    {%fol|star(a) * b = b|};
    {%fol|a * hash(a) = 1|};
    {%fol|hash(hash(a)) = a * 1|};
    {%fol|hash(hash(hash(a))) = hash(a)|}];;

  complete_and_simplify ["1"; "star"; "*"; "hash"; "dollar"] eqs;;

  ***********)

  (* ------------------------------------------------------------------------- *)
  (* Central groupoids II. (K&B example 16).                                   *)
  (* ------------------------------------------------------------------------- *)

  let eqs =
   [{%fol|(a * a) * a = one(a)|};
    {%fol|a * (a * a) = two(a)|};
    {%fol|(a * b) * (b * c) = b|};
    {%fol|two(a) * b = a * b|}];;

  complete_and_simplify ["one"; "two"; "*"] eqs;;

  (* ------------------------------------------------------------------------- *)
  (* Central groupoids II. (K&B example 17).                                   *)
  (* ------------------------------------------------------------------------- *)

  (******** Not ordered right...

  let eqs =
   [{%fol|(a*a * a) = one(a)|};
    {%fol|(a * a*a) = two(a)|};
    {%fol|(a*b * b*c) = b|}];;

  complete_and_simplify ["*"; "one"; "two"] eqs;;

   ************)

  (* ------------------------------------------------------------------------- *)
  (* Simply congruence closure.                                                *)
  (* ------------------------------------------------------------------------- *)

  let eqs =  [{%fol|f(f(f(f(f(1))))) = 1|}; {%fol|f(f(f(1))) = 1|}];;

  complete_and_simplify ["1"; "f"] eqs;;

  (* ------------------------------------------------------------------------- *)
  (* Bill McCune's and Deepak Kapur's single axioms for groups.                *)
  (* ------------------------------------------------------------------------- *)

  (*****************

  let eqs =
   [{%fol|x * i(y * (((z * i(z)) * i(u * y)) * x)) = u|}];;

  complete_and_simplify ["1"; "*"; "i"] eqs;;

  let eqs =
   [{%fol|((1 / (x / (y / (((x / x) / x) / z)))) / z) = y|}];;

  complete_and_simplify ["1"; "/"] eqs;;

  let eqs =
   [{%fol|i(x * i(x)) * (i(i((y * z) * u) * y) * i(u)) = z|}];;

  complete_and_simplify ["*"; "i"] eqs;;

  **************)

  (* ------------------------------------------------------------------------- *)
  (* A rather simple example from Baader & Nipkow, p. 141.                     *)
  (* ------------------------------------------------------------------------- *)

  let eqs =  [{%fol|f(f(x)) = g(x)|}];;

  complete_and_simplify ["g"; "f"] eqs;;
  [%expect {| |}]
;;


(* ------------------------------------------------------------------------- *)
(* Step-by-step; note that we *do* deduce commutativity, deferred of course. *)
(* ------------------------------------------------------------------------- *)

let eqs =
 [{%fol|(x * y) * z = x * (y * z)|}; {%fol|1 * x = x|}; {%fol|x * 1 = x|}; {%fol|x * x = 1|}]
and wts = ["1"; "*"; "i"];;

let ord = lpo_ge (weight wts);;

let def = [] and crits = unions(allpairs critical_pairs eqs eqs);;
let complete1 ord (eqs,def,crits) =
  match crits with
    (eq::ocrits) ->
        let trip =
          try let (s',t') = normalize_and_orient ord eqs eq in
              if s' = t' then (eqs,def,ocrits) else
              let eq' = Atom(R("=",[s';t'])) in
              let eqs' = eq'::eqs in
              eqs',def,
              ocrits @ itlist ((@) ** critical_pairs eq') eqs' []
          with Failure _ -> (eqs,eq::def,ocrits) in
        status trip eqs; trip
  | _ -> if def = [] then (eqs,def,crits) else
         let e = find (can (normalize_and_orient ord eqs)) def in
         (eqs,subtract def [e],[e]);;


(* ------------------------------------------------------------------------- *)
(* Some of the exercises (these are taken from Baader & Nipkow).             *)
(* ------------------------------------------------------------------------- *)

let%expect_test "eg: Some of the exercises (these are taken from Baader & Nipkow)" =
  let eqs =
   [{%fol|f(f(x)) = f(x)|};
    {%fol|g(g(x)) = f(x)|};
    {%fol|f(g(x)) = g(x)|};
    {%fol|g(f(x)) = f(x)|}] in
  print_list print_fol_formula
    (eqs);
  print_list print_fol_formula
    (complete_and_simplify ["f"; "g"] eqs);
  let eqs =  [{%fol|f(g(f(x))) = g(x)|}] in
  print_list print_fol_formula
    (eqs);
  print_list print_fol_formula
    (complete_and_simplify ["f"; "g"] eqs);
  (* ------------------------------------------------------------------------- *)
  (* Inductive theorem proving example.                                        *)
  (* ------------------------------------------------------------------------- *)
  let eqs =
   [{%fol|0 + y = y|};
    {%fol|SUC(x) + y = SUC(x + y)|};
    {%fol|append(nil,l) = l|};
    {%fol|append(h::t,l) = h::append(t,l)|};
    {%fol|length(nil) = 0|};
    {%fol|length(h::t) = SUC(length(t))|};
    {%fol|rev(nil) = nil|};
    {%fol|rev(h::t) = append(rev(t),h::nil)|}] in
  print_list print_fol_formula
    (eqs);
  print_list print_fol_formula
    (complete_and_simplify
       ["0"; "nil"; "SUC"; "::"; "+"; "length"; "append"; "rev"] eqs);
  let iprove eqs' tm =
   complete_and_simplify
     ["0"; "nil"; "SUC"; "::"; "+"; "append"; "rev"; "length"]
     (tm :: eqs' @ eqs) in
  print_fol_formula
    (iprove [] {%fol|x + 0 = x|});
  print_fol_formula
    (iprove [] {%fol|x + SUC(y) = SUC(x + y)|});
  print_fol_formula
    (iprove [] {%fol|(x + y) + z = x + y + z|});
  print_fol_formula
    (iprove [] {%fol|length(append(x,y)) = length(x) + length(y)|});
  print_fol_formula
    (iprove [] {%fol|append(append(x,y),z) = append(x,append(y,z))|});
  print_fol_formula
    (iprove [] {%fol|append(x,nil) = x|});
  print_fol_formula
    (iprove [{%fol|append(append(x,y),z) = append(x,append(y,z))|};
            {%fol|append(x,nil) = x|}]
            {%fol|rev(append(x,y)) = append(rev(y),rev(x))|});
  print_fol_formula
    (iprove [{%fol|rev(append(x,y)) = append(rev(y),rev(x))|};
            {%fol|append(x,nil) = x|};
            {%fol|append(append(x,y),z) = append(x,append(y,z))|}]
            {%fol|rev(rev(x)) = x|});
  (* ------------------------------------------------------------------------- *)
  (* Here it's not immediately so obvious since we get extra equs.             *)
  (* ------------------------------------------------------------------------- *)
  print_fol_formula
    (iprove [] {%fol|rev(rev(x)) = x|});
  (* ------------------------------------------------------------------------- *)
  (* With fewer lemmas, it may just need more or may not terminate.       *)
  (* ------------------------------------------------------------------------- *)

  (********* not enough lemmas...or maybe it just needs more runtime

  iprove [{%fol|rev(append(x,y)) = append(rev(y),rev(x))|}]
          {%fol|rev(rev(x)) = x|};;

   *********)

  (* ------------------------------------------------------------------------- *)
  (* Now something actually false...                                           *)
  (* ------------------------------------------------------------------------- *)
  print_fol_formula
    (iprove [] {%fol|length(append(x,y)) = length(x)|});
  (*** try something false ***)
  *************)
  [%expect {|
    [<<(a * b) * b * c = b>>]2 equations and 8 pending critical pairs + 0 deferred
    3 equations and 18 pending critical pairs + 0 deferred
    3 equations and 0 pending critical pairs + 0 deferred
    [<<(x3 * x0 * x1) * x1 = x0 * x1>>; <<x1 * (x1 * x2) * x5 = x1 * x2>>;
    <<(a * b) * b * c = b>>]Searching with depth limit 0Searching with depth limit 1Searching with depth limit 2Searching with depth limit 3Searching with depth limit 4Searching with depth limit 5
    Searching with depth limit 0Searching with depth limit 1Searching with depth limit 2Searching with depth limit 3Searching with depth limit 4
    [5; 4]<<~z = x * y \/ f_w(x,z) = y>>[<<f(a,a * b) = b>>; <<g(a * b,b) = a>>;
    <<1 * a = a>>; <<a * 1 = a>>]5 equations and 8 pending critical pairs + 0 deferred
    6 equations and 10 pending critical pairs + 0 deferred
    7 equations and 11 pending critical pairs + 0 deferred
    8 equations and 12 pending critical pairs + 0 deferred
    8 equations and 0 pending critical pairs + 0 deferred
    [<<g(x1,x1) = 1>>; <<g(x0,1) = x0>>; <<f(1,x1) = x1>>; <<f(x0,x0) = 1>>;
    <<f(a,a * b) = b>>; <<g(a * b,b) = a>>; <<1 * a = a>>; <<a * 1 = a>>][
    <<f(a,f(b,c,a),d) = c>>][<<f(a,f(b,c,a),d) = c>>; <<f(a,b,c) = g(a,b)>>;
    <<g(a,b) = h(b)>>]4 equations and 11 pending critical pairs + 0 deferred
    4 equations and 0 pending critical pairs + 0 deferred
    [<<h(h(x2)) = x2>>; <<f(a,b,c) = h(b)>>; <<g(a,b) = h(b)>>]
    |}]
;;
