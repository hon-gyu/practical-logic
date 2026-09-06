(* Interactive examples from tactics.ml, lifted out of the source by
   tools/migrate_to_modules.py.  Not compiled: these are meant to be
   pasted into a toplevel that has opened Atp.All. *)

let g0 = set_goal
 {%fol|(forall x. x <= x) /\
   (forall x y z. x <= y /\ y <= z ==> x <= z) /\
   (forall x y. f(x) <= y <=> x <= g(y))
   ==> (forall x y. x <= y ==> f(x) <= f(y)) /\
       (forall x y. x <= y ==> g(x) <= g(y))|};;

let g1 = imp_intro_tac "ant" g0;;

let g2 = conj_intro_tac g1;;

let g3 = funpow 2 (auto_tac by ["ant"]) g2;;

extract_thm g3;;

(* ------------------------------------------------------------------------- *)
(* All packaged up together.                                                 *)
(* ------------------------------------------------------------------------- *)

prove {%fol|(forall x. x <= x) /\
        (forall x y z. x <= y /\ y <= z ==> x <= z) /\
        (forall x y. f(x) <= y <=> x <= g(y))
        ==> (forall x y. x <= y ==> f(x) <= f(y)) /\
            (forall x y. x <= y ==> g(x) <= g(y))|}
      [imp_intro_tac "ant";
       conj_intro_tac;
       auto_tac by ["ant"];
       auto_tac by ["ant"]];;

(* ---- *)

(* Define here just in time for (interactive) use. See above. *)
let cases = disj_elim_tac "";;

let ewd954 = prove
 {%fol|(forall x y. x <= y <=> x * y = x) /\
   (forall x y. f(x * y) = f(x) * f(y))
   ==> forall x y. x <= y ==> f(x) <= f(y)|}
 [note("eq_sym",{%fol|forall x y. x = y ==> y = x|})
    using [eq_sym {%tm|x|} {%tm|y|}];
  note("eq_trans",{%fol|forall x y z. x = y /\ y = z ==> x = z|})
    using [eq_trans {%tm|x|} {%tm|y|} {%tm|z|}];
  note("eq_cong",{%fol|forall x y. x = y ==> f(x) = f(y)|})
    using [axiom_funcong "f" [{%tm|x|}] [{%tm|y|}]];
  assume ["le",{%fol|forall x y. x <= y <=> x * y = x|};
          "hom",{%fol|forall x y. f(x * y) = f(x) * f(y)|}];
  fix "x"; fix "y";
  assume ["xy",{%fol|x <= y|}];
  so have {%fol|x * y = x|} by ["le"];
  so have {%fol|f(x * y) = f(x)|} by ["eq_cong"];
  so have {%fol|f(x) = f(x * y)|} by ["eq_sym"];
  so have {%fol|f(x) = f(x) * f(y)|} by ["eq_trans"; "hom"];
  so have {%fol|f(x) * f(y) = f(x)|} by ["eq_sym"];
  so conclude {%fol|f(x) <= f(y)|} by ["le"];
  qed];;

(* ---- *)

prove
 {%fol|(exists x. p(x)) ==> (forall x. p(x) ==> p(f(x)))
   ==> exists y. p(f(f(f(f(y)))))|}
  [assume ["A",{%fol|exists x. p(x)|}];
   assume ["B",{%fol|forall x. p(x) ==> p(f(x))|}];
   note ("C",{%fol|forall x. p(x) ==> p(f(f(f(f(x)))))|})
   proof
    [have {%fol|forall x. p(x) ==> p(f(f(x)))|} by ["B"];
     so conclude {%fol|forall x. p(x) ==> p(f(f(f(f(x)))))|} at once;
     qed];
   consider ("a",{%fol|p(a)|}) by ["A"];
   take {%tm|a|};
   so conclude {%fol|p(f(f(f(f(a)))))|} by ["C"];
   qed];;

(* ------------------------------------------------------------------------- *)
(* Alternative formulation with lemma construct.                             *)
(* ------------------------------------------------------------------------- *)

let lemma (s,p) (Goals((asl,w)::gls,jfn) as gl) =
  Goals((asl,p)::((s,p)::asl,w)::gls,
        fun (thp::thw::oths) ->
            jfn(imp_unduplicate(imp_trans thp (shunt thw)) :: oths)) in
prove
 {%fol|(exists x. p(x)) ==> (forall x. p(x) ==> p(f(x)))
   ==> exists y. p(f(f(f(f(y)))))|}
  [assume ["A",{%fol|exists x. p(x)|}];
   assume ["B",{%fol|forall x. p(x) ==> p(f(x))|}];
   lemma ("C",{%fol|forall x. p(x) ==> p(f(f(f(f(x)))))|});
     have {%fol|forall x. p(x) ==> p(f(f(x)))|} by ["B"];
     so conclude {%fol|forall x. p(x) ==> p(f(f(f(f(x)))))|} at once;
     qed;
   consider ("a",{%fol|p(a)|}) by ["A"];
   take {%tm|a|};
   so conclude {%fol|p(f(f(f(f(a)))))|} by ["C"];
   qed];;

(* ------------------------------------------------------------------------- *)
(* Running a series of proof steps one by one on goals.                      *)
(* ------------------------------------------------------------------------- *)

let run prf g = itlist (fun f -> f) (rev prf) g;;

(* ------------------------------------------------------------------------- *)
(* LCF-style interactivity.                                                  *)
(* ------------------------------------------------------------------------- *)

let current_goal = ref[set_goal False];;

let g x = current_goal := [set_goal x]; hd(!current_goal);;

let e t = current_goal := (t(hd(!current_goal))::(!current_goal));
          hd(!current_goal);;

let es t = current_goal := (run t (hd(!current_goal))::(!current_goal));
           hd(!current_goal);;

let b() = current_goal := tl(!current_goal); hd(!current_goal);;

(* ------------------------------------------------------------------------- *)
(* Examples.                                                                 *)
(* ------------------------------------------------------------------------- *)

prove {%fol|p(a) ==> (forall x. p(x) ==> p(f(x)))
        ==> exists y. p(y) /\ p(f(y))|}
      [our thesis at once;
       qed];;

prove
 {%fol|(exists x. p(x)) ==> (forall x. p(x) ==> p(f(x)))
   ==> exists y. p(f(f(f(f(y)))))|}
  [assume ["A",{%fol|exists x. p(x)|}];
   assume ["B",{%fol|forall x. p(x) ==> p(f(x))|}];
   note ("C",{%fol|forall x. p(x) ==> p(f(f(f(f(x)))))|}) proof
    [have {%fol|forall x. p(x) ==> p(f(f(x)))|} by ["B"];
     so our thesis at once;
     qed];
   consider ("a",{%fol|p(a)|}) by ["A"];
   take {%tm|a|};
   so our thesis by ["C"];
   qed];;

prove {%fol|forall a. p(a) ==> (forall x. p(x) ==> p(f(x)))
                  ==> exists y. p(y) /\ p(f(y))|}
      [fix "c";
       assume ["A",{%fol|p(c)|}];
       assume ["B",{%fol|forall x. p(x) ==> p(f(x))|}];
       take {%tm|c|};
       conclude {%fol|p(c)|} by ["A"];
       note ("C",{%fol|p(c) ==> p(f(c))|}) by ["B"];
       so our thesis by ["C"; "A"];
       qed];;

prove {%fol|p(c) ==> (forall x. p(x) ==> p(f(x)))
                  ==> exists y. p(y) /\ p(f(y))|}
      [assume ["A",{%fol|p(c)|}];
       assume ["B",{%fol|forall x. p(x) ==> p(f(x))|}];
       take {%tm|c|};
       conclude {%fol|p(c)|} by ["A"];
       our thesis by ["A"; "B"];
       qed];;

prove {%fol|forall a. p(a) ==> (forall x. p(x) ==> p(f(x)))
                  ==> exists y. p(y) /\ p(f(y))|}
      [fix "c";
       assume ["A",{%fol|p(c)|}];
       assume ["B",{%fol|forall x. p(x) ==> p(f(x))|}];
       take {%tm|c|};
       conclude {%fol|p(c)|} by ["A"];
       note ("C",{%fol|p(c) ==> p(f(c))|}) by ["B"];
       our thesis by ["C"; "A"];
       qed];;

prove {%fol|forall a. p(a) ==> (forall x. p(x) ==> p(f(x)))
                  ==> exists y. p(y) /\ p(f(y))|}
      [fix "c";
       assume ["A",{%fol|p(c)|}];
       assume ["B",{%fol|forall x. p(x) ==> p(f(x))|}];
       take {%tm|c|};
       note ("D",{%fol|p(c)|}) by ["A"];
       note ("C",{%fol|p(c) ==> p(f(c))|}) by ["B"];
       our thesis by ["C"; "A"; "D"];
       qed];;


prove {%fol|(p(a) \/ p(b)) ==> q ==> exists y. p(y)|}
  [assume ["A",{%fol|p(a) \/ p(b)|}];
   assume ["",{%fol|q|}];
   cases {%fol|p(a) \/ p(b)|} by ["A"];
     take {%tm|a|};
     so our thesis at once;
     qed;

     take {%tm|b|};
     so our thesis at once;
     qed];;

prove
  {%fol|(p(a) \/ p(b)) /\ (forall x. p(x) ==> p(f(x))) ==> exists y. p(f(y))|}
  [assume ["base",{%fol|p(a) \/ p(b)|};
           "Step",{%fol|forall x. p(x) ==> p(f(x))|}];
   cases {%fol|p(a) \/ p(b)|} by ["base"];
     so note("A",{%fol|p(a)|}) at once;
     note ("X",{%fol|p(a) ==> p(f(a))|}) by ["Step"];
     take {%tm|a|};
     our thesis by ["A"; "X"];
     qed;

     take {%tm|b|};
     so our thesis by ["Step"];
     qed];;

prove
 {%fol|(exists x. p(x)) ==> (forall x. p(x) ==> p(f(x))) ==> exists y. p(f(y))|}
  [assume ["A",{%fol|exists x. p(x)|}];
   assume ["B",{%fol|forall x. p(x) ==> p(f(x))|}];
   consider ("a",{%fol|p(a)|}) by ["A"];
   so note ("concl",{%fol|p(f(a))|}) by ["B"];
   take {%tm|a|};
   our thesis by ["concl"];
   qed];;

prove {%fol|(forall x. p(x) ==> q(x)) ==> (forall x. q(x) ==> p(x))
       ==> (p(a) <=> q(a))|}
  [assume ["A",{%fol|forall x. p(x) ==> q(x)|}];
   assume ["B",{%fol|forall x. q(x) ==> p(x)|}];
   note ("von",{%fol|p(a) ==> q(a)|}) by ["A"];
   note ("bis",{%fol|q(a) ==> p(a)|}) by ["B"];
   our thesis by ["von"; "bis"];
   qed];;

(*** Mizar-like

prove
  {%fol|(p(a) \/ p(b)) /\ (forall x. p(x) ==> p(f(x))) ==> exists y. p(f(y))|}
  [assume ["A",{%fol|antecedent|}];
   note ("Step",{%fol|forall x. p(x) ==> p(f(x))|}) by ["A"];
   per_cases by ["A"];
     suppose ("base",{%fol|p(a)|});
     note ("X",{%fol|p(a) ==> p(f(a))|}) by ["Step"];
     take {%tm|a|};
     our thesis by ["base"; "X"];
     qed;

     suppose ("base",{%fol|p(b)|});
     our thesis by ["Step"; "base"];
     qed;
   endcase];;

*****)
