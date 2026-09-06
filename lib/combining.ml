open Lib
open Formulas
open Prop
open Defcnf
open Fol
open Skolem
open Equal
open Cong
open Cooper
open Real

(* Warnings the book's style trips in this file; the rest of the
   library compiles with them on.  See lib/dune. *)
[@@@warning "-8-32"]

(* ========================================================================= *)
(* Nelson-Oppen combined decision procedure.                                 *)
(*                                                                           *)
(* Copyright (c) 2003-2007, John Harrison. (See "LICENSE.txt" for details.)  *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Real language with decision procedure.                                    *)
(* ------------------------------------------------------------------------- *)

let real_lang =
  let fn = ["-",1; "+",2; "-",2; "*",2; "^",2]
  and pr = ["<=",2; "<",2; ">=",2; ">",2] in
  (fun (s,n) -> n = 0 && is_numeral(Fn(s,[])) || mem (s,n) fn),
  (fun sn -> mem sn pr),
  (fun fm -> real_qelim(generalize fm) = True);;

(* ------------------------------------------------------------------------- *)
(* Integer language with decision procedure.                                 *)
(* ------------------------------------------------------------------------- *)

let int_lang =
  let fn = ["-",1; "+",2; "-",2; "*",2]
  and pr = ["<=",2; "<",2; ">=",2; ">",2] in
  (fun (s,n) -> n = 0 && is_numeral(Fn(s,[])) || mem (s,n) fn),
  (fun sn -> mem sn pr),
  (fun fm -> integer_qelim(generalize fm) = True);;

(* ------------------------------------------------------------------------- *)
(* Add any uninterpreted functions to a list of languages.                   *)
(* ------------------------------------------------------------------------- *)

let add_default langs =
  langs @ [(fun sn -> not (exists (fun (f,p,d) -> f sn) langs)),
           (fun sn -> sn = ("=",2)),ccvalid];;

(* ------------------------------------------------------------------------- *)
(* Choose a language for homogenization of an atom.                          *)
(* ------------------------------------------------------------------------- *)

let chooselang langs fm =
  match fm with
    Atom(R("=",[Fn(f,args);_])) | Atom(R("=",[_;Fn(f,args)])) ->
        find (fun (fn,pr,dp) -> fn(f,length args)) langs
  | Atom(R(p,args)) ->
        find (fun (fn,pr,dp) -> pr(p,length args)) langs;;

(* ------------------------------------------------------------------------- *)
(* General listification for CPS-style function.                             *)
(* ------------------------------------------------------------------------- *)

let rec listify f l cont =
  match l with
    [] -> cont []
  | h::t -> f h (fun h' -> listify f t (fun t' -> cont(h'::t')));;

(* ------------------------------------------------------------------------- *)
(* Homogenize a term.                                                        *)
(* ------------------------------------------------------------------------- *)

let rec homot (fn,pr,dp) tm cont n defs =
  match tm with
    Var x -> cont tm n defs
  | Fn(f,args) ->
       if fn(f,length args) then
       listify (homot (fn,pr,dp)) args (fun a -> cont (Fn(f,a))) n defs
       else cont (Var("v_"^(string_of_num n))) (n +/ Int 1)
                 (mk_eq (Var("v_"^(string_of_num n))) tm :: defs);;

(* ------------------------------------------------------------------------- *)
(* Homogenize a literal.                                                     *)
(* ------------------------------------------------------------------------- *)

let rec homol langs fm cont n defs =
  match fm with
    Not(f) -> homol langs f (fun p -> cont(Not(p))) n defs
  | Atom(R(p,args)) ->
        let lang = chooselang langs fm in
        listify (homot lang) args (fun a -> cont (Atom(R(p,a)))) n defs
  | _ -> failwith "homol: not a literal";;

(* ------------------------------------------------------------------------- *)
(* Fully homogenize a list of literals.                                      *)
(* ------------------------------------------------------------------------- *)

let rec homo langs fms cont =
  listify (homol langs) fms
          (fun dun n defs ->
              if defs = [] then cont dun n defs
              else homo langs defs (fun res -> cont (dun@res)) n []);;

(* ------------------------------------------------------------------------- *)
(* Overall homogenization.                                                   *)
(* ------------------------------------------------------------------------- *)

let homogenize langs fms =
  let fvs = unions(map fv fms) in
  let n = Int 1 +/ itlist (max_varindex "v_") fvs (Int 0) in
  homo langs fms (fun res n defs -> res) n [];;

(* ------------------------------------------------------------------------- *)
(* Whether a formula belongs to a language.                                  *)
(* ------------------------------------------------------------------------- *)

let belongs (fn,pr,dp) fm =
  forall fn (functions fm) &&
  forall pr (subtract (predicates fm) ["=",2]);;

(* ------------------------------------------------------------------------- *)
(* Partition formulas among a list of languages.                             *)
(* ------------------------------------------------------------------------- *)

let rec langpartition langs fms =
  match langs with
    [] -> if fms = [] then [] else failwith "langpartition"
  | l::ls -> let fms1,fms2 = partition (belongs l) fms in
             fms1::langpartition ls fms2;;

(* ------------------------------------------------------------------------- *)
(* Running example if we magically knew the interpolant.                     *)
(* ------------------------------------------------------------------------- *)


(* ------------------------------------------------------------------------- *)
(* Turn an arrangement (partition) of variables into corresponding formula.  *)
(* ------------------------------------------------------------------------- *)

let rec arreq l =
  match l with
    v1::v2::rest -> mk_eq (Var v1) (Var v2) :: (arreq (v2::rest))
  | _ -> [];;

let arrangement part =
  itlist (union ** arreq) part
         (map (fun (v,w) -> Not(mk_eq (Var v) (Var w)))
              (distinctpairs (map hd part)));;

(* ------------------------------------------------------------------------- *)
(* Attempt to substitute with trivial equations.                             *)
(* ------------------------------------------------------------------------- *)

let dest_def fm =
  match fm with
    Atom(R("=",[Var x;t])) when not(mem x (fvt t)) -> x,t
  | Atom(R("=",[t; Var x])) when not(mem x (fvt t)) -> x,t
  | _ -> failwith "dest_def";;

let rec redeqs eqs =
  try let eq = find (can dest_def) eqs in
      let x,t = dest_def eq in
      redeqs (map (subst (x |=> t)) (subtract eqs [eq]))
  with Failure _ -> eqs;;

(* ------------------------------------------------------------------------- *)
(* Naive Nelson-Oppen variant trying all arrangements.                       *)
(* ------------------------------------------------------------------------- *)

let trydps ldseps fms =
  exists (fun ((_,_,dp),fms0) -> dp(Not(list_conj(redeqs(fms0 @ fms)))))
         ldseps;;

let allpartitions =
  let allinsertions x l acc =
    itlist (fun p acc -> ((x::p)::(subtract l [p])) :: acc) l
           (([x]::l)::acc) in
  fun l -> itlist (fun h y -> itlist (allinsertions h) y []) l [[]];;

let nelop_refute vars ldseps =
  forall (trydps ldseps ** arrangement) (allpartitions vars);;

let nelop1 langs fms0 =
  let fms = homogenize langs fms0 in
  let seps = langpartition langs fms in
  let fvlist = map (unions ** map fv) seps in
  let vars = filter (fun x -> length (filter (mem x) fvlist) >= 2)
                    (unions fvlist) in
  nelop_refute vars (zip langs seps);;

let nelop langs fm = forall (nelop1 langs) (simpdnf(simplify(Not fm)));;

(* ------------------------------------------------------------------------- *)
(* Check that our example works.                                             *)
(* ------------------------------------------------------------------------- *)


(* ------------------------------------------------------------------------- *)
(* Find the smallest subset satisfying a predicate.                          *)
(* ------------------------------------------------------------------------- *)

let rec findasubset p m l =
  if m = 0 then p [] else
  match l with
    [] -> failwith "findasubset"
  | h::t -> try findasubset (fun s -> p(h::s)) (m - 1) t
            with Failure _ -> findasubset p m t;;

let findsubset p l =
  tryfind (fun n ->
    findasubset (fun x -> if p x then x else failwith "") n l)
       (0--length l);;

(* ------------------------------------------------------------------------- *)
(* The "true" Nelson-Oppen method.                                           *)
(* ------------------------------------------------------------------------- *)

let rec nelop_refute eqs ldseps =
  try let dj = findsubset (trydps ldseps ** map negate) eqs in
      forall (fun eq ->
        nelop_refute (subtract eqs [eq])
                     (map (fun (dps,es) -> (dps,eq::es)) ldseps)) dj
  with Failure _ -> false;;

let nelop1 langs fms0 =
  let fms = homogenize langs fms0 in
  let seps = langpartition langs fms in
  let fvlist = map (unions ** map fv) seps in
  let vars = filter (fun x -> length (filter (mem x) fvlist) >= 2)
                    (unions fvlist) in
  let eqs = map (fun (a,b) -> mk_eq (Var a) (Var b))
                (distinctpairs vars) in
  nelop_refute eqs (zip langs seps);;

let nelop langs fm = forall (nelop1 langs) (simpdnf(simplify(Not fm)));;

(* ------------------------------------------------------------------------- *)
(* Some additional examples (from ICS paper and Shostak's "A practical..."   *)
(* ------------------------------------------------------------------------- *)
