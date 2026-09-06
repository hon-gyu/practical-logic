open Lib
open Formulas
open Prop
open Fol
open Skolem
open Qelim

(* Warnings the book's style trips in this file; the rest of the
   library compiles with them on.  See lib/dune. *)
[@@@warning "-8-39"]

(* ========================================================================= *)
(* Cooper's algorithm for Presburger arithmetic.                             *)
(*                                                                           *)
(* Copyright (c) 2003-2007, John Harrison. (See "LICENSE.txt" for details.)  *)
(* ========================================================================= *)

let zero = Fn("0",[]);;

(* ------------------------------------------------------------------------- *)
(* Lift operations up to numerals.                                           *)
(* ------------------------------------------------------------------------- *)

let mk_numeral n = Fn(string_of_num n,[]);;

let dest_numeral t =
  match t with
    Fn(ns,[]) -> num_of_string ns
  | _ -> failwith "dest_numeral";;

let is_numeral = can dest_numeral;;

let numeral1 fn n = mk_numeral(fn(dest_numeral n));;

let numeral2 fn m n = mk_numeral(fn (dest_numeral m) (dest_numeral n));;

(* ------------------------------------------------------------------------- *)
(* Operations on canonical linear terms c1 * x1 + ... + cn * xn + k          *)
(*                                                                           *)
(* Note that we're quite strict: the ci must be present even if 1            *)
(* (but if 0 we expect that variable to be omitted) and k must be there      *)
(* even if it's zero. Thus, it's a constant iff not an addition term.        *)
(* ------------------------------------------------------------------------- *)

let rec linear_cmul n tm =
  if n =/ Int 0 then zero else
  match tm with
    Fn("+",[Fn("*",[c; x]); r]) ->
        Fn("+",[Fn("*",[numeral1(( */ ) n) c; x]); linear_cmul n r])
  | k -> numeral1(( */ ) n) k;;

let rec linear_add vars tm1 tm2 =
  match (tm1,tm2) with
   (Fn("+",[Fn("*",[c1; Var x1]); r1]),
    Fn("+",[Fn("*",[c2; Var x2]); r2])) ->
        if x1 = x2 then
          let c = numeral2 (+/) c1 c2 in
          if c = zero then linear_add vars r1 r2
          else Fn("+",[Fn("*",[c; Var x1]); linear_add vars r1 r2])
        else if earlier vars x1 x2 then
          Fn("+",[Fn("*",[c1; Var x1]); linear_add vars r1 tm2])
        else
          Fn("+",[Fn("*",[c2; Var x2]); linear_add vars tm1 r2])
  | (Fn("+",[Fn("*",[c1; Var x1]); r1]),k2) ->
        Fn("+",[Fn("*",[c1; Var x1]); linear_add vars r1 k2])
  | (k1,Fn("+",[Fn("*",[c2; Var x2]); r2])) ->
        Fn("+",[Fn("*",[c2; Var x2]); linear_add vars k1 r2])
  | _ -> numeral2(+/) tm1 tm2;;

let linear_neg tm = linear_cmul (Int(-1)) tm;;

let linear_sub vars tm1 tm2 = linear_add vars tm1 (linear_neg tm2);;

let linear_mul tm1 tm2 =
  if is_numeral tm1 then linear_cmul (dest_numeral tm1) tm2
  else if is_numeral tm2 then linear_cmul (dest_numeral tm2) tm1
  else failwith "linear_mul: nonlinearity";;

(* ------------------------------------------------------------------------- *)
(* Linearize a term.                                                         *)
(* ------------------------------------------------------------------------- *)

let rec lint vars tm =
  match tm with
    Var(_) -> Fn("+",[Fn("*",[Fn("1",[]); tm]); zero])
  | Fn("-",[t]) -> linear_neg (lint vars t)
  | Fn("+",[s;t]) -> linear_add vars (lint vars s) (lint vars t)
  | Fn("-",[s;t]) -> linear_sub vars (lint vars s) (lint vars t)
  | Fn("*",[s;t]) -> linear_mul (lint vars s) (lint vars t)
  | _ -> if is_numeral tm then tm else failwith "lint: unknown term";;

(* ------------------------------------------------------------------------- *)
(* Linearize the atoms in a formula, and eliminate non-strict inequalities.  *)
(* ------------------------------------------------------------------------- *)

let mkatom vars p t = Atom(R(p,[zero; lint vars t]));;

let linform vars fm =
  match fm with
    Atom(R("divides",[c;t])) ->
        Atom(R("divides",[numeral1 abs_num c; lint vars t]))
  | Atom(R("=",[s;t])) -> mkatom vars "=" (Fn("-",[t;s]))
  | Atom(R("<",[s;t])) -> mkatom vars "<" (Fn("-",[t;s]))
  | Atom(R(">",[s;t])) -> mkatom vars "<" (Fn("-",[s;t]))
  | Atom(R("<=",[s;t])) ->
        mkatom vars "<" (Fn("-",[Fn("+",[t;Fn("1",[])]);s]))
  | Atom(R(">=",[s;t])) ->
        mkatom vars "<" (Fn("-",[Fn("+",[s;Fn("1",[])]);t]))
  | _ -> fm;;

(* ------------------------------------------------------------------------- *)
(* Post-NNF transformation eliminating negated inequalities.                 *)
(* ------------------------------------------------------------------------- *)

let rec posineq fm =
  match fm with
  | Not(Atom(R("<",[Fn("0",[]); t]))) ->
        Atom(R("<",[zero; linear_sub [] (Fn("1",[])) t]))
  | _ -> fm;;

(* ------------------------------------------------------------------------- *)
(* Find the LCM of the coefficients of x.                                    *)
(* ------------------------------------------------------------------------- *)

let rec formlcm x fm =
  match fm with
    Atom(R(p,[_;Fn("+",[Fn("*",[c;y]);z])])) when y = x ->
        abs_num(dest_numeral c)
  | Not(p) -> formlcm x p
  | And(p,q) | Or(p,q) -> lcm_num (formlcm x p) (formlcm x q)
  | _ -> Int 1;;

(* ------------------------------------------------------------------------- *)
(* Adjust all coefficients of x in formula; fold in reduction to +/- 1.      *)
(* ------------------------------------------------------------------------- *)

let rec adjustcoeff x l fm =
  match fm with
    Atom(R(p,[d; Fn("+",[Fn("*",[c;y]);z])])) when y = x ->
        let m = l // dest_numeral c in
        let n = if p = "<" then abs_num(m) else m in
        let xtm = Fn("*",[mk_numeral(m // n); x]) in
        Atom(R(p,[linear_cmul (abs_num m) d;
                  Fn("+",[xtm; linear_cmul n z])]))
  | Not(p) -> Not(adjustcoeff x l p)
  | And(p,q) -> And(adjustcoeff x l p,adjustcoeff x l q)
  | Or(p,q) -> Or(adjustcoeff x l p,adjustcoeff x l q)
  | _ -> fm;;

(* ------------------------------------------------------------------------- *)
(* Hence make coefficient of x one in existential formula.                   *)
(* ------------------------------------------------------------------------- *)

let unitycoeff x fm =
  let l = formlcm x fm in
  let fm' = adjustcoeff x l fm in
  if l =/ Int 1 then fm' else
  let xp = Fn("+",[Fn("*",[Fn("1",[]);x]); zero]) in
  And(Atom(R("divides",[mk_numeral l; xp])),adjustcoeff x l fm);;

(* ------------------------------------------------------------------------- *)
(* The "minus infinity" version.                                             *)
(* ------------------------------------------------------------------------- *)

let rec minusinf x fm =
  match fm with
    Atom(R("=",[Fn("0",[]); Fn("+",[Fn("*",[Fn("1",[]);y]);a])]))
        when y = x -> False
  | Atom(R("<",[Fn("0",[]); Fn("+",[Fn("*",[pm1;y]);a])])) when y = x ->
        if pm1 = Fn("1",[]) then False else True
  | Not(p) -> Not(minusinf x p)
  | And(p,q) -> And(minusinf x p,minusinf x q)
  | Or(p,q) -> Or(minusinf x p,minusinf x q)
  | _ -> fm;;

(* ------------------------------------------------------------------------- *)
(* The LCM of all the divisors that involve x.                               *)
(* ------------------------------------------------------------------------- *)

let rec divlcm x fm =
  match fm with
    Atom(R("divides",[d;Fn("+",[Fn("*",[c;y]);a])])) when y = x ->
        dest_numeral d
  | Not(p) -> divlcm x p
  | And(p,q) | Or(p,q) -> lcm_num (divlcm x p) (divlcm x q)
  | _ -> Int 1;;

(* ------------------------------------------------------------------------- *)
(* Construct the B-set.                                                      *)
(* ------------------------------------------------------------------------- *)

let rec bset x fm =
  match fm with
    Not(Atom(R("=",[Fn("0",[]); Fn("+",[Fn("*",[Fn("1",[]);y]);a])])))
    when y = x -> [linear_neg a]
  | Atom(R("=",[Fn("0",[]); Fn("+",[Fn("*",[Fn("1",[]);y]);a])]))
    when y = x -> [linear_neg(linear_add [] a (Fn("1",[])))]
  | Atom(R("<",[Fn("0",[]); Fn("+",[Fn("*",[Fn("1",[]);y]);a])]))
    when y = x -> [linear_neg a]
  | Not(p) -> bset x p
  | And(p,q) -> union (bset x p) (bset x q)
  | Or(p,q) -> union (bset x p) (bset x q)
  | _ -> [];;

(* ------------------------------------------------------------------------- *)
(* Replace top variable with another linear form, retaining canonicality.    *)
(* ------------------------------------------------------------------------- *)

let rec linrep vars x t fm =
  match fm with
    Atom(R(p,[d; Fn("+",[Fn("*",[c;y]);a])])) when y = x ->
        let ct = linear_cmul (dest_numeral c) t in
        Atom(R(p,[d; linear_add vars ct a]))
  | Not(p) -> Not(linrep vars x t p)
  | And(p,q) -> And(linrep vars x t p,linrep vars x t q)
  | Or(p,q) -> Or(linrep vars x t p,linrep vars x t q)
  | _ -> fm;;

(* ------------------------------------------------------------------------- *)
(* Hence the core quantifier elimination procedure.                          *)
(* ------------------------------------------------------------------------- *)

let cooper vars fm =
  match fm with
   Exists(x0,p0) ->
        let x = Var x0 in
        let p = unitycoeff x p0 in
        let p_inf = simplify(minusinf x p) and bs = bset x p
        and js = Int 1 --- divlcm x p in
        let p_element j b =
          linrep vars x (linear_add vars b (mk_numeral j)) p in
        let stage j = list_disj
           (linrep vars x (mk_numeral j) p_inf ::
            map (p_element j) bs) in
        list_disj (map stage js)
  | _ -> failwith "cooper: not an existential formula";;

(* ------------------------------------------------------------------------- *)
(* Evaluation of constant expressions.                                       *)
(* ------------------------------------------------------------------------- *)

let operations =
  ["=",(=/); "<",(</); ">",(>/); "<=",(<=/); ">=",(>=/);
   "divides",(fun x y -> mod_num y x =/ Int 0)];;

let evalc = onatoms
  (fun (R(p,[s;t]) as at) ->
        (try if assoc p operations (dest_numeral s) (dest_numeral t)
             then True else False
         with Failure _ -> Atom at));;

(* ------------------------------------------------------------------------- *)
(* Overall function.                                                         *)
(* ------------------------------------------------------------------------- *)

let integer_qelim =
  simplify ** evalc **
  lift_qelim linform (cnnf posineq ** evalc) cooper;;

(* ------------------------------------------------------------------------- *)
(* Examples.                                                                 *)
(* ------------------------------------------------------------------------- *)


(* ------------------------------------------------------------------------- *)
(* Natural number version.                                                   *)
(* ------------------------------------------------------------------------- *)

let rec relativize r fm =
  match fm with
    Not(p) -> Not(relativize r p)
  | And(p,q) -> And(relativize r p,relativize r q)
  | Or(p,q) -> Or(relativize r p,relativize r q)
  | Imp(p,q) -> Imp(relativize r p,relativize r q)
  | Iff(p,q) -> Iff(relativize r p,relativize r q)
  | Forall(x,p) -> Forall(x,Imp(r x,relativize r p))
  | Exists(x,p) -> Exists(x,And(r x,relativize r p))
  | _ -> fm;;

let natural_qelim =
  integer_qelim ** relativize(fun x -> Atom(R("<=",[zero; Var x])));;
