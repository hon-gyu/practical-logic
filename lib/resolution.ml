open Lib
open Formulas
open Prop
open Fol
open Skolem
open Unif
open Tableaux

(* Warnings the book's style trips in this file; the rest of the
   library compiles with them on.  See lib/dune. *)
[@@@warning "-32-39"]

(* ========================================================================= *)
(* Resolution.                                                               *)
(*                                                                           *)
(* Copyright (c) 2003-2007, John Harrison. (See "LICENSE.txt" for details.)  *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Barber's paradox is an example of why we need factoring.                  *)
(* ------------------------------------------------------------------------- *)

let barb = {%fol|~(exists b. forall x. shaves(b,x) <=> ~shaves(x,x))|};;


let%expect_test _ =
  print_list (print_list print_fol_formula)
    (simpcnf(skolemize(Not barb)));
  [%expect {| [[<<shaves(x,x)>>; <<shaves(c_b,x)>>]; [<<~shaves(x,x)>>; <<~shaves(c_b,x)>>]] |}]
;;

(* ------------------------------------------------------------------------- *)
(* MGU of a set of literals.                                                 *)
(* ------------------------------------------------------------------------- *)

let rec mgu l env =
  match l with
    a::b::rest -> mgu (b::rest) (unify_literals env (a,b))
  | _ -> solve env;;

let unifiable p q = can (unify_literals undefined) (p,q);;

(* ------------------------------------------------------------------------- *)
(* Rename a clause.                                                          *)
(* ------------------------------------------------------------------------- *)

let rename pfx cls =
  let fvs = fv(list_disj cls) in
  let vvs = map (fun s -> Var(pfx^s)) fvs  in
  map (subst(fpf fvs vvs)) cls;;

(* ------------------------------------------------------------------------- *)
(* General resolution rule, incorporating factoring as in Robinson's paper.  *)
(* ------------------------------------------------------------------------- *)

let resolvents cl1 cl2 p acc =
  let ps2 = filter (unifiable(negate p)) cl2 in
  if ps2 = [] then acc else
  let ps1 = filter (fun q -> q <> p && unifiable p q) cl1 in
  let pairs = allpairs (fun s1 s2 -> s1,s2)
                       (map (fun pl -> p::pl) (allsubsets ps1))
                       (allnonemptysubsets ps2) in
  itlist (fun (s1,s2) sof ->
           try image (subst (mgu (s1 @ map negate s2) undefined))
                     (union (subtract cl1 s1) (subtract cl2 s2)) :: sof
           with Failure _ -> sof) pairs acc;;

let resolve_clauses cls1 cls2 =
  let cls1' = rename "x" cls1 and cls2' = rename "y" cls2 in
  itlist (resolvents cls1' cls2') cls1' [];;

(* ------------------------------------------------------------------------- *)
(* Basic "Argonne" loop.                                                     *)
(* ------------------------------------------------------------------------- *)

let rec resloop (used,unused) =
  match unused with
    [] -> failwith "No proof found"
  | cl::ros ->
      print_string(string_of_int(length used) ^ " used; "^
                   string_of_int(length unused) ^ " unused.");
      print_newline();
      let used' = insert cl used in
      let news = itlist(@) (mapfilter (resolve_clauses cl) used') [] in
      if mem [] news then true else resloop (used',ros@news);;

let pure_resolution fm = resloop([],simpcnf(specialize(pnf fm)));;

let resolution fm =
  let fm1 = askolemize(Not(generalize fm)) in
  map (pure_resolution ** list_conj) (simpdnf fm1);;

(* ------------------------------------------------------------------------- *)
(* Simple example that works well.                                           *)
(* ------------------------------------------------------------------------- *)

let%expect_test "eg: Simple example that works well" =
  let davis_putnam_example = resolution
   {%fol|exists x. exists y. forall z.
          (F(x,y) ==> (F(y,z) /\ F(z,z))) /\
          ((F(x,y) /\ G(x,y)) ==> (G(x,z) /\ G(z,z)))|} in
  print_list print_bool
    (davis_putnam_example);
  [%expect {|
    0 used; 3 unused.
    1 used; 2 unused.
    2 used; 3 unused.
    3 used; 6 unused.
    4 used; 8 unused.
    5 used; 10 unused.
    6 used; 16 unused.
    7 used; 22 unused.
    8 used; 28 unused.
    9 used; 34 unused.
    10 used; 41 unused.
    11 used; 47 unused.
    12 used; 53 unused.
    13 used; 62 unused.
    14 used; 69 unused.
    15 used; 76 unused.
    16 used; 85 unused.
    17 used; 92 unused.
    18 used; 99 unused.
    19 used; 105 unused.
    20 used; 111 unused.
    21 used; 117 unused.
    22 used; 123 unused.
    23 used; 132 unused.
    24 used; 139 unused.
    25 used; 146 unused.
    26 used; 152 unused.
    27 used; 158 unused.
    28 used; 164 unused.
    29 used; 170 unused.
    30 used; 177 unused.
    31 used; 184 unused.
    32 used; 191 unused.
    33 used; 198 unused.
    34 used; 203 unused.
    35 used; 207 unused.
    36 used; 211 unused.
    37 used; 218 unused.
    37 used; 225 unused.
    38 used; 232 unused.
    39 used; 239 unused.
    40 used; 244 unused.
    41 used; 248 unused.
    42 used; 252 unused.
    43 used; 255 unused.
    44 used; 260 unused.
    45 used; 265 unused.
    46 used; 268 unused.
    47 used; 274 unused.
    48 used; 280 unused.
    49 used; 285 unused.
    50 used; 290 unused.
    51 used; 296 unused.
    52 used; 302 unused.
    53 used; 308 unused.
    54 used; 312 unused.
    55 used; 315 unused.
    56 used; 318 unused.
    57 used; 320 unused.
    58 used; 326 unused.
    59 used; 332 unused.
    60 used; 338 unused.
    61 used; 342 unused.
    62 used; 345 unused.
    63 used; 348 unused.
    64 used; 350 unused.
    64 used; 353 unused.
    64 used; 358 unused.
    64 used; 363 unused.
    64 used; 366 unused.
    64 used; 372 unused.
    64 used; 378 unused.
    65 used; 380 unused.
    66 used; 382 unused.
    66 used; 387 unused.
    66 used; 392 unused.
    67 used; 398 unused.
    68 used; 404 unused.
    68 used; 410 unused.
    69 used; 414 unused.
    70 used; 417 unused.
    71 used; 420 unused.
    72 used; 422 unused.
    72 used; 424 unused.
    73 used; 430 unused.
    74 used; 436 unused.
    74 used; 442 unused.
    75 used; 446 unused.
    76 used; 449 unused.
    77 used; 452 unused.
    78 used; 454 unused.
    78 used; 456 unused.
    79 used; 462 unused.
    80 used; 468 unused.
    81 used; 473 unused.
    82 used; 478 unused.
    83 used; 483 unused.
    84 used; 488 unused.
    [true]
    |}]
;;


(* ------------------------------------------------------------------------- *)
(* Matching of terms and literals.                                           *)
(* ------------------------------------------------------------------------- *)

let rec term_match env eqs =
  match eqs with
    [] -> env
  | (Fn(f,fa),Fn(g,ga))::oth when f = g && length fa = length ga ->
        term_match env (zip fa ga @ oth)
  | (Var x,t)::oth ->
        if not (defined env x) then term_match ((x |-> t) env) oth
        else if apply env x = t then term_match env oth
        else failwith "term_match"
  | _ -> failwith "term_match";;

let rec match_literals env tmp =
  match tmp with
    Atom(R(p,a1)),Atom(R(q,a2)) | Not(Atom(R(p,a1))),Not(Atom(R(q,a2))) ->
       term_match env [Fn(p,a1),Fn(q,a2)]
  | _ -> failwith "match_literals";;

(* ------------------------------------------------------------------------- *)
(* Test for subsumption                                                      *)
(* ------------------------------------------------------------------------- *)

let subsumes_clause cls1 cls2 =
  let rec subsume env cls =
    match cls with
      [] -> env
    | l1::clt ->
        tryfind (fun l2 -> subsume (match_literals env (l1,l2)) clt)
                cls2 in
  can (subsume undefined) cls1;;

(* ------------------------------------------------------------------------- *)
(* With deletion of tautologies and bi-subsumption with "unused".            *)
(* ------------------------------------------------------------------------- *)

let rec replace cl lis =
  match lis with
    [] -> [cl]
  | c::cls -> if subsumes_clause cl c then cl::cls
              else c::(replace cl cls);;

let incorporate gcl cl unused =
  if trivial cl ||
     exists (fun c -> subsumes_clause c cl) (gcl::unused)
  then unused else replace cl unused;;

let rec resloop (used,unused) =
  match unused with
    [] -> failwith "No proof found"
  | cl::ros ->
      print_string(string_of_int(length used) ^ " used; "^
                   string_of_int(length unused) ^ " unused.");
      print_newline();
      let used' = insert cl used in
      let news = itlist(@) (mapfilter (resolve_clauses cl) used') [] in
      if mem [] news then true
      else resloop(used',itlist (incorporate cl) news ros);;

let pure_resolution fm = resloop([],simpcnf(specialize(pnf fm)));;

let resolution fm =
  let fm1 = askolemize(Not(generalize fm)) in
  map (pure_resolution ** list_conj) (simpdnf fm1);;

(* ------------------------------------------------------------------------- *)
(* This is now a lot quicker.                                                *)
(* ------------------------------------------------------------------------- *)

let%expect_test "eg: This is now a lot quicker" =
  let davis_putnam_example = resolution
   {%fol|exists x. exists y. forall z.
          (F(x,y) ==> (F(y,z) /\ F(z,z))) /\
          ((F(x,y) /\ G(x,y)) ==> (G(x,z) /\ G(z,z)))|} in
  print_list print_bool
    (davis_putnam_example);
  [%expect {|
    0 used; 3 unused.
    1 used; 2 unused.
    2 used; 3 unused.
    3 used; 6 unused.
    4 used; 5 unused.
    5 used; 4 unused.
    6 used; 3 unused.
    7 used; 2 unused.
    [true]
    |}]
;;


(* ------------------------------------------------------------------------- *)
(* Positive (P1) resolution.                                                 *)
(* ------------------------------------------------------------------------- *)

let presolve_clauses cls1 cls2 =
  if forall positive cls1 || forall positive cls2
  then resolve_clauses cls1 cls2 else [];;

let rec presloop (used,unused) =
  match unused with
    [] -> failwith "No proof found"
  | cl::ros ->
      print_string(string_of_int(length used) ^ " used; "^
                   string_of_int(length unused) ^ " unused.");
      print_newline();
      let used' = insert cl used in
      let news = itlist(@) (mapfilter (presolve_clauses cl) used') [] in
      if mem [] news then true else
      presloop(used',itlist (incorporate cl) news ros);;

let pure_presolution fm = presloop([],simpcnf(specialize(pnf fm)));;

let presolution fm =
  let fm1 = askolemize(Not(generalize fm)) in
  map (pure_presolution ** list_conj) (simpdnf fm1);;

let%expect_test "eg: the (in)famous Los problem" =
  let los = presolution
   {%fol|(forall x y z. P(x,y) ==> P(y,z) ==> P(x,z)) /\
     (forall x y z. Q(x,y) ==> Q(y,z) ==> Q(x,z)) /\
     (forall x y. Q(x,y) ==> Q(y,x)) /\
     (forall x y. P(x,y) \/ Q(x,y))
     ==> (forall x y. P(x,y)) \/ (forall x y. Q(x,y))|} in
  print_list print_bool
    (los);
  (* ------------------------------------------------------------------------- *)
  (* Introduce a set-of-support restriction.                                   *)
  (* ------------------------------------------------------------------------- *)
  let pure_resolution fm =
    resloop(partition (exists positive) (simpcnf(specialize(pnf fm)))) in
  let resolution fm =
    let fm1 = askolemize(Not(generalize fm)) in
    map (pure_resolution ** list_conj) (simpdnf fm1) in
  (* ------------------------------------------------------------------------- *)
  (* The Pelletier examples again.                                             *)
  (* ------------------------------------------------------------------------- *)

  (***********

  let p1 = presolution
   {%fol|p ==> q <=> ~q ==> ~p|};;

  let p2 = presolution
   {%fol|~ ~p <=> p|};;

  let p3 = presolution
   {%fol|~(p ==> q) ==> q ==> p|};;

  let p4 = presolution
   {%fol|~p ==> q <=> ~q ==> p|};;

  let p5 = presolution
   {%fol|(p \/ q ==> p \/ r) ==> p \/ (q ==> r)|};;

  let p6 = presolution
   {%fol|p \/ ~p|};;

  let p7 = presolution
   {%fol|p \/ ~ ~ ~p|};;

  let p8 = presolution
   {%fol|((p ==> q) ==> p) ==> p|};;

  let p9 = presolution
   {%fol|(p \/ q) /\ (~p \/ q) /\ (p \/ ~q) ==> ~(~q \/ ~q)|};;

  let p10 = presolution
   {%fol|(q ==> r) /\ (r ==> p /\ q) /\ (p ==> q /\ r) ==> (p <=> q)|};;

  let p11 = presolution
   {%fol|p <=> p|};;

  let p12 = presolution
   {%fol|((p <=> q) <=> r) <=> (p <=> (q <=> r))|};;

  let p13 = presolution
   {%fol|p \/ q /\ r <=> (p \/ q) /\ (p \/ r)|};;

  let p14 = presolution
   {%fol|(p <=> q) <=> (q \/ ~p) /\ (~q \/ p)|};;

  let p15 = presolution
   {%fol|p ==> q <=> ~p \/ q|};;

  let p16 = presolution
   {%fol|(p ==> q) \/ (q ==> p)|};;

  let p17 = presolution
   {%fol|p /\ (q ==> r) ==> s <=> (~p \/ q \/ s) /\ (~p \/ ~r \/ s)|};;

  (* ------------------------------------------------------------------------- *)
  (* Monadic Predicate Logic.                                                  *)
  (* ------------------------------------------------------------------------- *)

  let p18 = presolution
   {%fol|exists y. forall x. P(y) ==> P(x)|};;

  let p19 = presolution
   {%fol|exists x. forall y z. (P(y) ==> Q(z)) ==> P(x) ==> Q(x)|};;

  let p20 = presolution
   {%fol|(forall x y. exists z. forall w. P(x) /\ Q(y) ==> R(z) /\ U(w))
     ==> (exists x y. P(x) /\ Q(y)) ==> (exists z. R(z))|};;

  let p21 = presolution
   {%fol|(exists x. P ==> Q(x)) /\ (exists x. Q(x) ==> P)
     ==> (exists x. P <=> Q(x))|};;

  let p22 = presolution
   {%fol|(forall x. P <=> Q(x)) ==> (P <=> (forall x. Q(x)))|};;

  let p23 = presolution
   {%fol|(forall x. P \/ Q(x)) <=> P \/ (forall x. Q(x))|};;

  let p24 = presolution
   {%fol|~(exists x. U(x) /\ Q(x)) /\
     (forall x. P(x) ==> Q(x) \/ R(x)) /\
     ~(exists x. P(x) ==> (exists x. Q(x))) /\
     (forall x. Q(x) /\ R(x) ==> U(x)) ==>
     (exists x. P(x) /\ R(x))|};;

  let p25 = presolution
   {%fol|(exists x. P(x)) /\
     (forall x. U(x) ==> ~G(x) /\ R(x)) /\
     (forall x. P(x) ==> G(x) /\ U(x)) /\
     ((forall x. P(x) ==> Q(x)) \/ (exists x. Q(x) /\ P(x))) ==>
     (exists x. Q(x) /\ P(x))|};;

  let p26 = presolution
   {%fol|((exists x. P(x)) <=> (exists x. Q(x))) /\
     (forall x y. P(x) /\ Q(y) ==> (R(x) <=> U(y))) ==>
     ((forall x. P(x) ==> R(x)) <=> (forall x. Q(x) ==> U(x)))|};;

  let p27 = presolution
   {%fol|(exists x. P(x) /\ ~Q(x)) /\
     (forall x. P(x) ==> R(x)) /\
     (forall x. U(x) /\ V(x) ==> P(x)) /\
     (exists x. R(x) /\ ~Q(x)) ==>
     (forall x. U(x) ==> ~R(x)) ==>
     (forall x. U(x) ==> ~V(x))|};;

  let p28 = presolution
   {%fol|(forall x. P(x) ==> (forall x. Q(x))) /\
     ((forall x. Q(x) \/ R(x)) ==> (exists x. Q(x) /\ R(x))) /\
     ((exists x. R(x)) ==> (forall x. L(x) ==> M(x))) ==>
     (forall x. P(x) /\ L(x) ==> M(x))|};;

  let p29 = presolution
   {%fol|(exists x. P(x)) /\ (exists x. G(x)) ==>
     ((forall x. P(x) ==> H(x)) /\ (forall x. G(x) ==> J(x)) <=>
      (forall x y. P(x) /\ G(y) ==> H(x) /\ J(y)))|};;

  let p30 = presolution
   {%fol|(forall x. P(x) \/ G(x) ==> ~H(x)) /\
     (forall x. (G(x) ==> ~U(x)) ==> P(x) /\ H(x)) ==>
     (forall x. U(x))|};;

  let p31 = presolution
   {%fol|~(exists x. P(x) /\ (G(x) \/ H(x))) /\ (exists x. Q(x) /\ P(x)) /\
     (forall x. ~H(x) ==> J(x)) ==>
     (exists x. Q(x) /\ J(x))|};;

  let p32 = presolution
   {%fol|(forall x. P(x) /\ (G(x) \/ H(x)) ==> Q(x)) /\
     (forall x. Q(x) /\ H(x) ==> J(x)) /\
     (forall x. R(x) ==> H(x)) ==>
     (forall x. P(x) /\ R(x) ==> J(x))|};;

  let p33 = presolution
   {%fol|(forall x. P(a) /\ (P(x) ==> P(b)) ==> P(c)) <=>
     (forall x. P(a) ==> P(x) \/ P(c)) /\ (P(a) ==> P(b) ==> P(c))|};;

  let p34 = presolution
   {%fol|((exists x. forall y. P(x) <=> P(y)) <=>
      ((exists x. Q(x)) <=> (forall y. Q(y)))) <=>
     ((exists x. forall y. Q(x) <=> Q(y)) <=>
      ((exists x. P(x)) <=> (forall y. P(y))))|};;

  let p35 = presolution
   {%fol|exists x y. P(x,y) ==> (forall x y. P(x,y))|};;

  (* ------------------------------------------------------------------------- *)
  (*  Full predicate logic (without Identity and Functions)                    *)
  (* ------------------------------------------------------------------------- *)

  let p36 = presolution
   {%fol|(forall x. exists y. P(x,y)) /\
     (forall x. exists y. G(x,y)) /\
     (forall x y. P(x,y) \/ G(x,y)
     ==> (forall z. P(y,z) \/ G(y,z) ==> H(x,z)))
         ==> (forall x. exists y. H(x,y))|};;

  let p37 = presolution
   {%fol|(forall z.
       exists w. forall x. exists y. (P(x,z) ==> P(y,w)) /\ P(y,z) /\
       (P(y,w) ==> (exists u. Q(u,w)))) /\
     (forall x z. ~P(x,z) ==> (exists y. Q(y,z))) /\
     ((exists x y. Q(x,y)) ==> (forall x. R(x,x))) ==>
     (forall x. exists y. R(x,y))|};;

  (*** This one seems too slow

  let p38 = presolution
   {%fol|(forall x.
       P(a) /\ (P(x) ==> (exists y. P(y) /\ R(x,y))) ==>
       (exists z w. P(z) /\ R(x,w) /\ R(w,z))) <=>
     (forall x.
       (~P(a) \/ P(x) \/ (exists z w. P(z) /\ R(x,w) /\ R(w,z))) /\
       (~P(a) \/ ~(exists y. P(y) /\ R(x,y)) \/
       (exists z w. P(z) /\ R(x,w) /\ R(w,z))))|};;

   ***)

  let p39 = presolution
   {%fol|~(exists x. forall y. P(y,x) <=> ~P(y,y))|};;

  let p40 = presolution
   {%fol|(exists y. forall x. P(x,y) <=> P(x,x))
    ==> ~(forall x. exists y. forall z. P(z,y) <=> ~P(z,x))|};;

  let p41 = presolution
   {%fol|(forall z. exists y. forall x. P(x,y) <=> P(x,z) /\ ~P(x,x))
    ==> ~(exists z. forall x. P(x,z))|};;

  (*** Also very slow

  let p42 = presolution
   {%fol|~(exists y. forall x. P(x,y) <=> ~(exists z. P(x,z) /\ P(z,x)))|};;

   ***)

  (*** and this one too..

  let p43 = presolution
   {%fol|(forall x y. Q(x,y) <=> forall z. P(z,x) <=> P(z,y))
     ==> forall x y. Q(x,y) <=> Q(y,x)|};;

   ***)

  let p44 = presolution
   {%fol|(forall x. P(x) ==> (exists y. G(y) /\ H(x,y)) /\
     (exists y. G(y) /\ ~H(x,y))) /\
     (exists x. J(x) /\ (forall y. G(y) ==> H(x,y))) ==>
     (exists x. J(x) /\ ~P(x))|};;

  (*** and this...

  let p45 = presolution
   {%fol|(forall x.
       P(x) /\ (forall y. G(y) /\ H(x,y) ==> J(x,y)) ==>
         (forall y. G(y) /\ H(x,y) ==> R(y))) /\
     ~(exists y. L(y) /\ R(y)) /\
     (exists x. P(x) /\ (forall y. H(x,y) ==>
       L(y)) /\ (forall y. G(y) /\ H(x,y) ==> J(x,y))) ==>
     (exists x. P(x) /\ ~(exists y. G(y) /\ H(x,y)))|};;

   ***)

  (*** and this

  let p46 = presolution
   {%fol|(forall x. P(x) /\ (forall y. P(y) /\ H(y,x) ==> G(y)) ==> G(x)) /\
     ((exists x. P(x) /\ ~G(x)) ==>
      (exists x. P(x) /\ ~G(x) /\
                 (forall y. P(y) /\ ~G(y) ==> J(x,y)))) /\
     (forall x y. P(x) /\ P(y) /\ H(x,y) ==> ~J(y,x)) ==>
     (forall x. P(x) ==> G(x))|};;

   ***)

  (* ------------------------------------------------------------------------- *)
  (* Example from Manthey and Bry, CADE-9.                                     *)
  (* ------------------------------------------------------------------------- *)

  let p55 = presolution
   {%fol|lives(agatha) /\ lives(butler) /\ lives(charles) /\
     (killed(agatha,agatha) \/ killed(butler,agatha) \/
      killed(charles,agatha)) /\
     (forall x y. killed(x,y) ==> hates(x,y) /\ ~richer(x,y)) /\
     (forall x. hates(agatha,x) ==> ~hates(charles,x)) /\
     (hates(agatha,agatha) /\ hates(agatha,charles)) /\
     (forall x. lives(x) /\ ~richer(x,agatha) ==> hates(butler,x)) /\
     (forall x. hates(agatha,x) ==> hates(butler,x)) /\
     (forall x. ~hates(x,agatha) \/ ~hates(x,butler) \/ ~hates(x,charles))
     ==> killed(agatha,agatha) /\
         ~killed(butler,agatha) /\
         ~killed(charles,agatha)|};;

  let p57 = presolution
   {%fol|P(f((a),b),f(b,c)) /\
     P(f(b,c),f(a,c)) /\
     (forall (x) y z. P(x,y) /\ P(y,z) ==> P(x,z))
     ==> P(f(a,b),f(a,c))|};;

  (* ------------------------------------------------------------------------- *)
  (* See info-hol, circa 1500.                                                 *)
  (* ------------------------------------------------------------------------- *)

  let p58 = presolution
   {%fol|forall P Q R. forall x. exists v. exists w. forall y. forall z.
      ((P(x) /\ Q(y)) ==> ((P(v) \/ R(w))  /\ (R(z) ==> Q(v))))|};;

  let p59 = presolution
   {%fol|(forall x. P(x) <=> ~P(f(x))) ==> (exists x. P(x) /\ ~P(f(x)))|};;

  let p60 = presolution
   {%fol|forall x. P(x,f(x)) <=>
              exists y. (forall z. P(z,y) ==> P(z,f(x))) /\ P(x,y)|};;

  (* ------------------------------------------------------------------------- *)
  (* From Gilmore's classic paper.                                             *)
  (* ------------------------------------------------------------------------- *)

  let gilmore_1 = presolution
   {%fol|exists x. forall y z.
        ((F(y) ==> G(y)) <=> F(x)) /\
        ((F(y) ==> H(y)) <=> G(x)) /\
        (((F(y) ==> G(y)) ==> H(y)) <=> H(x))
        ==> F(z) /\ G(z) /\ H(z)|};;

  (*** This is not valid, according to Gilmore

  let gilmore_2 = presolution
   {%fol|exists x y. forall z.
          (F(x,z) <=> F(z,y)) /\ (F(z,y) <=> F(z,z)) /\ (F(x,y) <=> F(y,x))
          ==> (F(x,y) <=> F(x,z))|};;

   ***)

  let gilmore_3 = presolution
   {%fol|exists x. forall y z.
          ((F(y,z) ==> (G(y) ==> H(x))) ==> F(x,x)) /\
          ((F(z,x) ==> G(x)) ==> H(z)) /\
          F(x,y)
          ==> F(z,z)|};;

  let gilmore_4 = presolution
   {%fol|exists x y. forall z.
          (F(x,y) ==> F(y,z) /\ F(z,z)) /\
          (F(x,y) /\ G(x,y) ==> G(x,z) /\ G(z,z))|};;

  let gilmore_5 = presolution
   {%fol|(forall x. exists y. F(x,y) \/ F(y,x)) /\
     (forall x y. F(y,x) ==> F(y,y))
     ==> exists z. F(z,z)|};;

  let gilmore_6 = presolution
   {%fol|forall x. exists y.
          (exists u. forall v. F(u,x) ==> G(v,u) /\ G(u,x))
          ==> (exists u. forall v. F(u,y) ==> G(v,u) /\ G(u,y)) \/
              (forall u v. exists w. G(v,u) \/ H(w,y,u) ==> G(u,w))|};;

  let gilmore_7 = presolution
   {%fol|(forall x. K(x) ==> exists y. L(y) /\ (F(x,y) ==> G(x,y))) /\
     (exists z. K(z) /\ forall u. L(u) ==> F(z,u))
     ==> exists v w. K(v) /\ L(w) /\ G(v,w)|};;

  let gilmore_8 = presolution
   {%fol|exists x. forall y z.
          ((F(y,z) ==> (G(y) ==> (forall u. exists v. H(u,v,x)))) ==> F(x,x)) /\
          ((F(z,x) ==> G(x)) ==> (forall u. exists v. H(u,v,z))) /\
          F(x,y)
          ==> F(z,z)|};;

  (*** This one still isn't easy!

  let gilmore_9 = presolution
   {%fol|forall x. exists y. forall z.
          ((forall u. exists v. F(y,u,v) /\ G(y,u) /\ ~H(y,x))
            ==> (forall u. exists v. F(x,u,v) /\ G(z,u) /\ ~H(x,z))
               ==> (forall u. exists v. F(x,u,v) /\ G(y,u) /\ ~H(x,y))) /\
          ((forall u. exists v. F(x,u,v) /\ G(y,u) /\ ~H(x,y))
           ==> ~(forall u. exists v. F(x,u,v) /\ G(z,u) /\ ~H(x,z))
               ==> (forall u. exists v. F(y,u,v) /\ G(y,u) /\ ~H(y,x)) /\
                   (forall u. exists v. F(z,u,v) /\ G(y,u) /\ ~H(z,y)))|};;

   ***)

  (* ------------------------------------------------------------------------- *)
  (* Example from Davis-Putnam papers where Gilmore procedure is poor.         *)
  (* ------------------------------------------------------------------------- *)

  let davis_putnam_example = presolution
   {%fol|exists x. exists y. forall z.
          (F(x,y) ==> (F(y,z) /\ F(z,z))) /\
          ((F(x,y) /\ G(x,y)) ==> (G(x,z) /\ G(z,z)))|};;

  ************)
  [%expect {|
    0 used; 6 unused.
    1 used; 5 unused.
    2 used; 7 unused.
    3 used; 8 unused.
    4 used; 7 unused.
    5 used; 7 unused.
    6 used; 7 unused.
    7 used; 13 unused.
    8 used; 14 unused.
    9 used; 14 unused.
    10 used; 15 unused.
    11 used; 15 unused.
    12 used; 18 unused.
    13 used; 21 unused.
    14 used; 24 unused.
    15 used; 28 unused.
    16 used; 33 unused.
    17 used; 35 unused.
    18 used; 36 unused.
    19 used; 38 unused.
    20 used; 39 unused.
    21 used; 48 unused.
    22 used; 47 unused.
    23 used; 48 unused.
    24 used; 47 unused.
    25 used; 46 unused.
    26 used; 46 unused.
    27 used; 46 unused.
    28 used; 46 unused.
    29 used; 45 unused.
    30 used; 44 unused.
    31 used; 44 unused.
    32 used; 44 unused.
    33 used; 43 unused.
    34 used; 42 unused.
    35 used; 41 unused.
    [true]
    |}]
;;


let%expect_test "eg" =
  let gilmore_1 = resolution
   {%fol|exists x. forall y z.
        ((F(y) ==> G(y)) <=> F(x)) /\
        ((F(y) ==> H(y)) <=> G(x)) /\
        (((F(y) ==> G(y)) ==> H(y)) <=> H(x))
        ==> F(z) /\ G(z) /\ H(z)|} in
  print_list print_bool
    (gilmore_1);
  (* ------------------------------------------------------------------------- *)
  (* Pelletiers yet again.                                                     *)
  (* ------------------------------------------------------------------------- *)

  (************

  let p1 = resolution
   {%fol|p ==> q <=> ~q ==> ~p|};;

  let p2 = resolution
   {%fol|~ ~p <=> p|};;

  let p3 = resolution
   {%fol|~(p ==> q) ==> q ==> p|};;

  let p4 = resolution
   {%fol|~p ==> q <=> ~q ==> p|};;

  let p5 = resolution
   {%fol|(p \/ q ==> p \/ r) ==> p \/ (q ==> r)|};;

  let p6 = resolution
   {%fol|p \/ ~p|};;

  let p7 = resolution
   {%fol|p \/ ~ ~ ~p|};;

  let p8 = resolution
   {%fol|((p ==> q) ==> p) ==> p|};;

  let p9 = resolution
   {%fol|(p \/ q) /\ (~p \/ q) /\ (p \/ ~q) ==> ~(~q \/ ~q)|};;

  let p10 = resolution
   {%fol|(q ==> r) /\ (r ==> p /\ q) /\ (p ==> q /\ r) ==> (p <=> q)|};;

  let p11 = resolution
   {%fol|p <=> p|};;

  let p12 = resolution
   {%fol|((p <=> q) <=> r) <=> (p <=> (q <=> r))|};;

  let p13 = resolution
   {%fol|p \/ q /\ r <=> (p \/ q) /\ (p \/ r)|};;

  let p14 = resolution
   {%fol|(p <=> q) <=> (q \/ ~p) /\ (~q \/ p)|};;

  let p15 = resolution
   {%fol|p ==> q <=> ~p \/ q|};;

  let p16 = resolution
   {%fol|(p ==> q) \/ (q ==> p)|};;

  let p17 = resolution
   {%fol|p /\ (q ==> r) ==> s <=> (~p \/ q \/ s) /\ (~p \/ ~r \/ s)|};;

  (* ------------------------------------------------------------------------- *)
  (* Monadic Predicate Logic.                                                  *)
  (* ------------------------------------------------------------------------- *)

  let p18 = resolution
   {%fol|exists y. forall x. P(y) ==> P(x)|};;

  let p19 = resolution
   {%fol|exists x. forall y z. (P(y) ==> Q(z)) ==> P(x) ==> Q(x)|};;

  let p20 = resolution
   {%fol|(forall x y. exists z. forall w. P(x) /\ Q(y) ==> R(z) /\ U(w)) ==>
     (exists x y. P(x) /\ Q(y)) ==>
     (exists z. R(z))|};;

  let p21 = resolution
   {%fol|(exists x. P ==> Q(x)) /\ (exists x. Q(x) ==> P) ==> (exists x. P <=> Q(x))|};;

  let p22 = resolution
   {%fol|(forall x. P <=> Q(x)) ==> (P <=> (forall x. Q(x)))|};;

  let p23 = resolution
   {%fol|(forall x. P \/ Q(x)) <=> P \/ (forall x. Q(x))|};;

  let p24 = resolution
   {%fol|~(exists x. U(x) /\ Q(x)) /\
     (forall x. P(x) ==> Q(x) \/ R(x)) /\
     ~(exists x. P(x) ==> (exists x. Q(x))) /\
     (forall x. Q(x) /\ R(x) ==> U(x)) ==>
     (exists x. P(x) /\ R(x))|};;

  let p25 = resolution
   {%fol|(exists x. P(x)) /\
     (forall x. U(x) ==> ~G(x) /\ R(x)) /\
     (forall x. P(x) ==> G(x) /\ U(x)) /\
     ((forall x. P(x) ==> Q(x)) \/ (exists x. Q(x) /\ P(x))) ==>
     (exists x. Q(x) /\ P(x))|};;

  let p26 = resolution
   {%fol|((exists x. P(x)) <=> (exists x. Q(x))) /\
     (forall x y. P(x) /\ Q(y) ==> (R(x) <=> U(y))) ==>
     ((forall x. P(x) ==> R(x)) <=> (forall x. Q(x) ==> U(x)))|};;

  let p27 = resolution
   {%fol|(exists x. P(x) /\ ~Q(x)) /\
     (forall x. P(x) ==> R(x)) /\
     (forall x. U(x) /\ V(x) ==> P(x)) /\
     (exists x. R(x) /\ ~Q(x)) ==>
     (forall x. U(x) ==> ~R(x)) ==>
     (forall x. U(x) ==> ~V(x))|};;

  let p28 = resolution
   {%fol|(forall x. P(x) ==> (forall x. Q(x))) /\
     ((forall x. Q(x) \/ R(x)) ==> (exists x. Q(x) /\ R(x))) /\
     ((exists x. R(x)) ==> (forall x. L(x) ==> M(x))) ==>
     (forall x. P(x) /\ L(x) ==> M(x))|};;

  let p29 = resolution
   {%fol|(exists x. P(x)) /\ (exists x. G(x)) ==>
     ((forall x. P(x) ==> H(x)) /\ (forall x. G(x) ==> J(x)) <=>
      (forall x y. P(x) /\ G(y) ==> H(x) /\ J(y)))|};;

  let p30 = resolution
   {%fol|(forall x. P(x) \/ G(x) ==> ~H(x)) /\ (forall x. (G(x) ==> ~U(x)) ==>
       P(x) /\ H(x)) ==>
     (forall x. U(x))|};;

  let p31 = resolution
   {%fol|~(exists x. P(x) /\ (G(x) \/ H(x))) /\ (exists x. Q(x) /\ P(x)) /\
     (forall x. ~H(x) ==> J(x)) ==>
     (exists x. Q(x) /\ J(x))|};;

  let p32 = resolution
   {%fol|(forall x. P(x) /\ (G(x) \/ H(x)) ==> Q(x)) /\
     (forall x. Q(x) /\ H(x) ==> J(x)) /\
     (forall x. R(x) ==> H(x)) ==>
     (forall x. P(x) /\ R(x) ==> J(x))|};;

  let p33 = resolution
   {%fol|(forall x. P(a) /\ (P(x) ==> P(b)) ==> P(c)) <=>
     (forall x. P(a) ==> P(x) \/ P(c)) /\ (P(a) ==> P(b) ==> P(c))|};;

  let p34 = resolution
   {%fol|((exists x. forall y. P(x) <=> P(y)) <=>
     ((exists x. Q(x)) <=> (forall y. Q(y)))) <=>
     ((exists x. forall y. Q(x) <=> Q(y)) <=>
    ((exists x. P(x)) <=> (forall y. P(y))))|};;

  let p35 = resolution
   {%fol|exists x y. P(x,y) ==> (forall x y. P(x,y))|};;

  (* ------------------------------------------------------------------------- *)
  (*  Full predicate logic (without Identity and Functions)                    *)
  (* ------------------------------------------------------------------------- *)

  let p36 = resolution
   {%fol|(forall x. exists y. P(x,y)) /\
     (forall x. exists y. G(x,y)) /\
     (forall x y. P(x,y) \/ G(x,y)
     ==> (forall z. P(y,z) \/ G(y,z) ==> H(x,z)))
         ==> (forall x. exists y. H(x,y))|};;

  let p37 = resolution
   {%fol|(forall z.
       exists w. forall x. exists y. (P(x,z) ==> P(y,w)) /\ P(y,z) /\
       (P(y,w) ==> (exists u. Q(u,w)))) /\
     (forall x z. ~P(x,z) ==> (exists y. Q(y,z))) /\
     ((exists x y. Q(x,y)) ==> (forall x. R(x,x))) ==>
     (forall x. exists y. R(x,y))|};;

  (*** This one seems too slow

  let p38 = resolution
   {%fol|(forall x.
       P(a) /\ (P(x) ==> (exists y. P(y) /\ R(x,y))) ==>
       (exists z w. P(z) /\ R(x,w) /\ R(w,z))) <=>
     (forall x.
       (~P(a) \/ P(x) \/ (exists z w. P(z) /\ R(x,w) /\ R(w,z))) /\
       (~P(a) \/ ~(exists y. P(y) /\ R(x,y)) \/
       (exists z w. P(z) /\ R(x,w) /\ R(w,z))))|};;

   ***)

  let p39 = resolution
   {%fol|~(exists x. forall y. P(y,x) <=> ~P(y,y))|};;

  let p40 = resolution
   {%fol|(exists y. forall x. P(x,y) <=> P(x,x))
    ==> ~(forall x. exists y. forall z. P(z,y) <=> ~P(z,x))|};;

  let p41 = resolution
   {%fol|(forall z. exists y. forall x. P(x,y) <=> P(x,z) /\ ~P(x,x))
    ==> ~(exists z. forall x. P(x,z))|};;

  (*** Also very slow

  let p42 = resolution
   {%fol|~(exists y. forall x. P(x,y) <=> ~(exists z. P(x,z) /\ P(z,x)))|};;

   ***)

  (*** and this one too..

  let p43 = resolution
   {%fol|(forall x y. Q(x,y) <=> forall z. P(z,x) <=> P(z,y))
     ==> forall x y. Q(x,y) <=> Q(y,x)|};;

   ***)

  let p44 = resolution
   {%fol|(forall x. P(x) ==> (exists y. G(y) /\ H(x,y)) /\
     (exists y. G(y) /\ ~H(x,y))) /\
     (exists x. J(x) /\ (forall y. G(y) ==> H(x,y))) ==>
     (exists x. J(x) /\ ~P(x))|};;

  (*** and this...

  let p45 = resolution
   {%fol|(forall x.
       P(x) /\ (forall y. G(y) /\ H(x,y) ==> J(x,y)) ==>
         (forall y. G(y) /\ H(x,y) ==> R(y))) /\
     ~(exists y. L(y) /\ R(y)) /\
     (exists x. P(x) /\ (forall y. H(x,y) ==>
       L(y)) /\ (forall y. G(y) /\ H(x,y) ==> J(x,y))) ==>
     (exists x. P(x) /\ ~(exists y. G(y) /\ H(x,y)))|};;

   ***)

  (*** and this

  let p46 = resolution
   {%fol|(forall x. P(x) /\ (forall y. P(y) /\ H(y,x) ==> G(y)) ==> G(x)) /\
     ((exists x. P(x) /\ ~G(x)) ==>
      (exists x. P(x) /\ ~G(x) /\
                 (forall y. P(y) /\ ~G(y) ==> J(x,y)))) /\
     (forall x y. P(x) /\ P(y) /\ H(x,y) ==> ~J(y,x)) ==>
     (forall x. P(x) ==> G(x))|};;

   ***)

  (* ------------------------------------------------------------------------- *)
  (* Example from Manthey and Bry, CADE-9.                                     *)
  (* ------------------------------------------------------------------------- *)

  let p55 = resolution
   {%fol|lives(agatha) /\ lives(butler) /\ lives(charles) /\
     (killed(agatha,agatha) \/ killed(butler,agatha) \/
      killed(charles,agatha)) /\
     (forall x y. killed(x,y) ==> hates(x,y) /\ ~richer(x,y)) /\
     (forall x. hates(agatha,x) ==> ~hates(charles,x)) /\
     (hates(agatha,agatha) /\ hates(agatha,charles)) /\
     (forall x. lives(x) /\ ~richer(x,agatha) ==> hates(butler,x)) /\
     (forall x. hates(agatha,x) ==> hates(butler,x)) /\
     (forall x. ~hates(x,agatha) \/ ~hates(x,butler) \/ ~hates(x,charles))
     ==> killed(agatha,agatha) /\
         ~killed(butler,agatha) /\
         ~killed(charles,agatha)|};;

  let p57 = resolution
   {%fol|P(f((a),b),f(b,c)) /\
     P(f(b,c),f(a,c)) /\
     (forall (x) y z. P(x,y) /\ P(y,z) ==> P(x,z))
     ==> P(f(a,b),f(a,c))|};;

  (* ------------------------------------------------------------------------- *)
  (* See info-hol, circa 1500.                                                 *)
  (* ------------------------------------------------------------------------- *)

  let p58 = resolution
   {%fol|forall P Q R. forall x. exists v. exists w. forall y. forall z.
      ((P(x) /\ Q(y)) ==> ((P(v) \/ R(w))  /\ (R(z) ==> Q(v))))|};;

  let p59 = resolution
   {%fol|(forall x. P(x) <=> ~P(f(x))) ==> (exists x. P(x) /\ ~P(f(x)))|};;

  let p60 = resolution
   {%fol|forall x. P(x,f(x)) <=>
              exists y. (forall z. P(z,y) ==> P(z,f(x))) /\ P(x,y)|};;

  (* ------------------------------------------------------------------------- *)
  (* From Gilmore's classic paper.                                             *)
  (* ------------------------------------------------------------------------- *)

  let gilmore_1 = resolution
   {%fol|exists x. forall y z.
        ((F(y) ==> G(y)) <=> F(x)) /\
        ((F(y) ==> H(y)) <=> G(x)) /\
        (((F(y) ==> G(y)) ==> H(y)) <=> H(x))
        ==> F(z) /\ G(z) /\ H(z)|};;

  (*** This is not valid, according to Gilmore

  let gilmore_2 = resolution
   {%fol|exists x y. forall z.
          (F(x,z) <=> F(z,y)) /\ (F(z,y) <=> F(z,z)) /\ (F(x,y) <=> F(y,x))
          ==> (F(x,y) <=> F(x,z))|};;

   ***)

  let gilmore_3 = resolution
   {%fol|exists x. forall y z.
          ((F(y,z) ==> (G(y) ==> H(x))) ==> F(x,x)) /\
          ((F(z,x) ==> G(x)) ==> H(z)) /\
          F(x,y)
          ==> F(z,z)|};;

  let gilmore_4 = resolution
   {%fol|exists x y. forall z.
          (F(x,y) ==> F(y,z) /\ F(z,z)) /\
          (F(x,y) /\ G(x,y) ==> G(x,z) /\ G(z,z))|};;

  let gilmore_5 = resolution
   {%fol|(forall x. exists y. F(x,y) \/ F(y,x)) /\
     (forall x y. F(y,x) ==> F(y,y))
     ==> exists z. F(z,z)|};;

  let gilmore_6 = resolution
   {%fol|forall x. exists y.
          (exists u. forall v. F(u,x) ==> G(v,u) /\ G(u,x))
          ==> (exists u. forall v. F(u,y) ==> G(v,u) /\ G(u,y)) \/
              (forall u v. exists w. G(v,u) \/ H(w,y,u) ==> G(u,w))|};;

  let gilmore_7 = resolution
   {%fol|(forall x. K(x) ==> exists y. L(y) /\ (F(x,y) ==> G(x,y))) /\
     (exists z. K(z) /\ forall u. L(u) ==> F(z,u))
     ==> exists v w. K(v) /\ L(w) /\ G(v,w)|};;

  let gilmore_8 = resolution
   {%fol|exists x. forall y z.
          ((F(y,z) ==> (G(y) ==> (forall u. exists v. H(u,v,x)))) ==> F(x,x)) /\
          ((F(z,x) ==> G(x)) ==> (forall u. exists v. H(u,v,z))) /\
          F(x,y)
          ==> F(z,z)|};;

  (*** This one still isn't easy!

  let gilmore_9 = resolution
   {%fol|forall x. exists y. forall z.
          ((forall u. exists v. F(y,u,v) /\ G(y,u) /\ ~H(y,x))
            ==> (forall u. exists v. F(x,u,v) /\ G(z,u) /\ ~H(x,z))
               ==> (forall u. exists v. F(x,u,v) /\ G(y,u) /\ ~H(x,y))) /\
          ((forall u. exists v. F(x,u,v) /\ G(y,u) /\ ~H(x,y))
           ==> ~(forall u. exists v. F(x,u,v) /\ G(z,u) /\ ~H(x,z))
               ==> (forall u. exists v. F(y,u,v) /\ G(y,u) /\ ~H(y,x)) /\
                   (forall u. exists v. F(z,u,v) /\ G(y,u) /\ ~H(z,y)))|};;

   ***)

  (* ------------------------------------------------------------------------- *)
  (* Example from Davis-Putnam papers where Gilmore procedure is poor.         *)
  (* ------------------------------------------------------------------------- *)

  let davis_putnam_example = resolution
   {%fol|exists x. exists y. forall z.
          (F(x,y) ==> (F(y,z) /\ F(z,z))) /\
          ((F(x,y) /\ G(x,y)) ==> (G(x,z) /\ G(z,z)))|};;

  (* ------------------------------------------------------------------------- *)
  (* The (in)famous Los problem.                                               *)
  (* ------------------------------------------------------------------------- *)

  let los = resolution
   {%fol|(forall x y z. P(x,y) ==> P(y,z) ==> P(x,z)) /\
     (forall x y z. Q(x,y) ==> Q(y,z) ==> Q(x,z)) /\
     (forall x y. Q(x,y) ==> Q(y,x)) /\
     (forall x y. P(x,y) \/ Q(x,y))
     ==> (forall x y. P(x,y)) \/ (forall x y. Q(x,y))|};;

  **************)
  [%expect {|
    0 used; 11 unused.
    1 used; 10 unused.
    2 used; 9 unused.
    3 used; 9 unused.
    4 used; 9 unused.
    5 used; 10 unused.
    6 used; 15 unused.
    7 used; 20 unused.
    8 used; 22 unused.
    9 used; 29 unused.
    10 used; 36 unused.
    11 used; 41 unused.
    12 used; 49 unused.
    13 used; 55 unused.
    14 used; 57 unused.
    15 used; 62 unused.
    16 used; 73 unused.
    17 used; 78 unused.
    18 used; 88 unused.
    19 used; 96 unused.
    20 used; 95 unused.
    21 used; 95 unused.
    22 used; 99 unused.
    23 used; 103 unused.
    24 used; 108 unused.
    25 used; 119 unused.
    26 used; 120 unused.
    27 used; 124 unused.
    28 used; 140 unused.
    29 used; 146 unused.
    30 used; 158 unused.
    31 used; 173 unused.
    32 used; 180 unused.
    33 used; 185 unused.
    34 used; 185 unused.
    35 used; 184 unused.
    36 used; 186 unused.
    36 used; 185 unused.
    37 used; 187 unused.
    38 used; 186 unused.
    39 used; 190 unused.
    40 used; 190 unused.
    41 used; 190 unused.
    42 used; 190 unused.
    43 used; 191 unused.
    44 used; 190 unused.
    45 used; 189 unused.
    46 used; 188 unused.
    47 used; 189 unused.
    48 used; 189 unused.
    49 used; 188 unused.
    50 used; 191 unused.
    51 used; 193 unused.
    52 used; 192 unused.
    53 used; 191 unused.
    54 used; 192 unused.
    55 used; 192 unused.
    56 used; 191 unused.
    57 used; 192 unused.
    57 used; 192 unused.
    58 used; 191 unused.
    59 used; 190 unused.
    [true]
    |}]
;;
