open Lib
open Formulas
open Fol
open Skolem
open Unif
open Tableaux
open Resolution
open Order
open Eqelim
open Lcf
open Lcfprop
open Folderived

(* Warnings the book's style trips in this file; the rest of the
   library compiles with them on.  See lib/dune. *)
[@@@warning "-8"]

(* ========================================================================= *)
(* First order tableau procedure using LCF setup.                            *)
(*                                                                           *)
(* Copyright (c) 2003-2007, John Harrison. (See "LICENSE.txt" for details.)  *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Unification of complementary literals.                                    *)
(* ------------------------------------------------------------------------- *)

let unify_complementsf env =
  function (Atom(R(p1,a1)),Imp(Atom(R(p2,a2)),False))
         | (Imp(Atom(R(p1,a1)),False),Atom(R(p2,a2)))
               -> unify env [Fn(p1,a1),Fn(p2,a2)]
         | _ -> failwith "unify_complementsf";;

(* ------------------------------------------------------------------------- *)
(*    |- (q ==> f) ==> ... ==> (q ==> p) ==> r                               *)
(* --------------------------------------------- use_laterimp {%fol|q ==> p|}    *)
(*    |- (p ==> f) ==> ... ==> (q ==> p) ==> r                               *)
(* ------------------------------------------------------------------------- *)

let rec use_laterimp i fm =
  match fm with
    Imp(Imp(q',s),Imp(Imp(q,p) as i',r)) when i' = i ->
        let th1 = axiom_distribimp i (Imp(Imp(q,s),r)) (Imp(Imp(p,s),r))
        and th2 = imp_swap(imp_trans_th q p s)
        and th3 = imp_swap(imp_trans_th (Imp(p,s)) (Imp(q,s)) r) in
        imp_swap2(modusponens th1 (imp_trans th2 th3))
  | Imp(qs,Imp(a,b)) ->
        imp_swap2(imp_add_assum a (use_laterimp i (Imp(qs,b))));;

(* ------------------------------------------------------------------------- *)
(* The "closure" inference rules.                                            *)
(* ------------------------------------------------------------------------- *)

let imp_false_rule' th es = imp_false_rule(th es);;

let imp_true_rule' th1 th2 es = imp_true_rule (th1 es) (th2 es);;

let imp_front' n thp es = imp_front n (thp es);;

let add_assum' fm thp (e,s as es) =
  add_assum (onformula e fm) (thp es);;

let eliminate_connective' fm thp (e,s as es) =
  imp_trans (eliminate_connective (onformula e fm)) (thp es);;

let spec' y fm n thp (e,s) =
  let th = imp_swap(imp_front n (thp(e,s))) in
  imp_unduplicate(imp_trans (ispec (e y) (onformula e fm)) th);;

let ex_falso' fms (e,s) =
  ex_falso (itlist (mk_imp ** onformula e) fms s);;

let complits' (p::fl,lits) i (e,s) =
  let l1,p'::l2 = chop_list i lits in
  itlist (imp_insert ** onformula e) (fl @ l1)
         (imp_contr (onformula e p)
                    (itlist (mk_imp ** onformula e) l2 s));;

let deskol' (skh:fol formula) thp (e,s) =
  let th = thp (e,s) in
  modusponens (use_laterimp (onformula e skh) (concl th)) th;;

(* ------------------------------------------------------------------------- *)
(* Main refutation function.                                                 *)
(* ------------------------------------------------------------------------- *)

let rec lcftab skofun (fms,lits,n) cont (env,sks,k as esk) =
  if n < 0 then failwith "lcftab: no proof" else
  match fms with
    False::fl -> cont (ex_falso' (fl @ lits)) esk
  | (Imp(p,q) as fm)::fl when p = q ->
      lcftab skofun (fl,lits,n) (cont ** add_assum' fm) esk
  | Imp(Imp(p,q),False)::fl ->
      lcftab skofun (p::Imp(q,False)::fl,lits,n)
                    (cont ** imp_false_rule') esk
  | Imp(p,q)::fl when q <> False ->
      lcftab skofun (Imp(p,False)::fl,lits,n)
        (fun th -> lcftab skofun (q::fl,lits,n)
                                 (cont ** imp_true_rule' th)) esk
  | ((Atom(_)|Imp(Atom(_),False)) as p)::fl ->
      (try tryfind (fun p' ->
          let env' = unify_complementsf env (p,p') in
          cont(complits' (fms,lits) (index p' lits)) (env',sks,k)) lits
       with Failure _ ->
          lcftab skofun (fl,p::lits,n)
                        (cont ** imp_front' (length fl)) esk)
  | (Forall(x,p) as fm)::fl ->
      let y = Var("X_"^string_of_int k) in
      lcftab skofun ((subst (x |=> y) p)::fl@[fm],lits,n-1)
                    (cont ** spec' y fm (length fms)) (env,sks,k+1)
  | (Imp(Forall(y,p) as yp,False))::fl ->
      let fx = skofun yp in
      let p' = subst(y |=> fx) p in
      let skh = Imp(p',Forall(y,p)) in
      let sks' = (Forall(y,p),fx)::sks in
      lcftab skofun (Imp(p',False)::fl,lits,n)
                    (cont ** deskol' skh) (env,sks',k)
  | fm::fl ->
      let fm' = consequent(concl(eliminate_connective fm)) in
      lcftab skofun (fm'::fl,lits,n)
                    (cont ** eliminate_connective' fm) esk
  | [] -> failwith "lcftab: No contradiction";;

(* ------------------------------------------------------------------------- *)
(* Identify quantified subformulas; true = exists, false = forall. This is   *)
(* taking into account the effective parity.                                 *)
(* NB: maybe I can use this in sigma/delta/pi determination.                 *)
(* ------------------------------------------------------------------------- *)

let rec quantforms e fm =
  match fm with
    Not(p) -> quantforms (not e) p
  | And(p,q) | Or(p,q) -> union (quantforms e p) (quantforms e q)
  | Imp(p,q) -> quantforms e (Or(Not p,q))
  | Iff(p,q) -> quantforms e (Or(And(p,q),And(Not p,Not q)))
  | Exists(x,p) -> if e then fm::(quantforms e p) else quantforms e p
  | Forall(x,p) -> if e then quantforms e p else fm::(quantforms e p)
  | _ -> [];;

(* ------------------------------------------------------------------------- *)
(* Now create some Skolem functions.                                         *)
(* ------------------------------------------------------------------------- *)

let skolemfuns fm =
  let fns = map fst (functions fm)
  and skts = map (function Exists(x,p) -> Forall(x,Not p) | p -> p)
                 (quantforms true fm) in
  let skofun i (Forall(y,p) as ap) =
    let vars = map (fun v -> Var v) (fv ap) in
    ap,Fn(variant("f"^"_"^string_of_int i) fns,vars) in
  map2 skofun (1--length skts) skts;;

(* ------------------------------------------------------------------------- *)
(* Matching.                                                                 *)
(* ------------------------------------------------------------------------- *)

let rec form_match (f1,f2 as fp) env =
  match fp with
    False,False | True,True -> env
  | Atom(R(p,pa)),Atom(R(q,qa)) -> term_match env [Fn(p,pa),Fn(q,qa)]
  | Not(p1),Not(p2) -> form_match (p1,p2) env
  | And(p1,q1),And(p2,q2)| Or(p1,q1),Or(p2,q2) | Imp(p1,q1),Imp(p2,q2)
  | Iff(p1,q1),Iff(p2,q2) -> form_match (p1,p2) (form_match (q1,q2) env)
  | (Forall(x1,p1),Forall(x2,p2) |
     Exists(x1,p1),Exists(x2,p2)) when x1 = x2 ->
        let z = variant x1 (union (fv p1) (fv p2)) in
        let inst_fn = subst (x1 |=> Var z) in
        undefine z (form_match (inst_fn p1,inst_fn p2) env)
  | _ -> failwith "form_match";;

(* ------------------------------------------------------------------------- *)
(* With the current approach to picking Skolem functions.                    *)
(* ------------------------------------------------------------------------- *)

let lcfrefute fm n cont =
  let sl = skolemfuns fm in
  let find_skolem fm =
    tryfind(fun (f,t) -> tsubst(form_match (f,fm) undefined) t) sl in
  lcftab find_skolem ([fm],[],n) cont (undefined,[],0);;

(* ------------------------------------------------------------------------- *)
(* A quick demo before doing deskolemization.                                *)
(* ------------------------------------------------------------------------- *)

let mk_skol (Forall(y,p),fx) q =
  Imp(Imp(subst (y |=> fx) p,Forall(y,p)),q);;

let simpcont thp (env,sks,k) =
  let ifn = tsubst(solve env) in
  thp(ifn,onformula ifn (itlist mk_skol sks False));;

lcfrefute {%fol|p(1) /\ ~q(1) /\ (forall x. p(x) ==> q(x))|} 1 simpcont;;

lcfrefute {%fol|(exists x. ~p(x)) /\ (forall x. p(x))|} 1 simpcont;;

(* ------------------------------------------------------------------------- *)
(*         |- (p(v) ==> forall x. p(x)) ==> q                                *)
(*       -------------------------------------- elim_skolemvar               *)
(*                   |- q                                                    *)
(* ------------------------------------------------------------------------- *)

let elim_skolemvar th =
  match concl th with
    Imp(Imp(pv,(Forall(x,px) as apx)),q) ->
        let [th1;th2] = map (imp_trans(imp_add_concl False th))
                            (imp_false_conseqs pv apx) in
        let v = hd(subtract (fv pv) (fv apx) @ [x]) in
        let th3 = gen_right v th1 in
        let th4 = imp_trans th3 (alpha x (consequent(concl th3))) in
        modusponens (axiom_doubleneg q) (right_mp th2 th4)
  | _ -> failwith "elim_skolemvar";;

(* ------------------------------------------------------------------------- *)
(* Top continuation with careful sorting and variable replacement.           *)
(* Also need to delete post-instantiation duplicates! This shows up more     *)
(* often now that we have adequate sharing.                                  *)
(* ------------------------------------------------------------------------- *)

let deskolcont thp (env,sks,k) =
  let ifn = tsubst(solve env) in
  let isk = setify(map (fun (p,t) -> onformula ifn p,ifn t) sks) in
  let ssk = sort (decreasing (termsize ** snd)) isk in
  let vs = map (fun i -> Var("Y_"^string_of_int i)) (1--length ssk) in
  let vfn =
    replacet(itlist2 (fun (p,t) v -> t |-> v) ssk vs undefined) in
  let th = thp(vfn ** ifn,onformula vfn (itlist mk_skol ssk False)) in
  repeat (elim_skolemvar ** imp_swap) th;;

(* ------------------------------------------------------------------------- *)
(* Overall first-order prover.                                               *)
(* ------------------------------------------------------------------------- *)

let lcffol fm =
  let fvs = fv fm in
  let fm' = Imp(itlist mk_forall fvs fm,False) in
  print_string "Proving ";
  print_fol_formula fm;
  print_newline ();
  let th1 = deepen (fun n -> lcfrefute fm' n deskolcont) 0 in
  let th2 = modusponens (axiom_doubleneg (negatef fm')) th1 in
  itlist (fun v -> spec(Var v)) (rev fvs) th2;;

(* ------------------------------------------------------------------------- *)
(* Examples in the text.                                                     *)
(* ------------------------------------------------------------------------- *)


(* ------------------------------------------------------------------------- *)
(* More exhaustive set of tests not in the main text.                        *)
(* ------------------------------------------------------------------------- *)
