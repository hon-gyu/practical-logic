open Lib
open Formulas
open Fol
open Resolution

(* ========================================================================= *)
(* Rewriting.                                                                *)
(*                                                                           *)
(* Copyright (c) 2003-2007, John Harrison. (See "LICENSE.txt" for details.)  *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Rewriting at the top level with first of list of equations.               *)
(* ------------------------------------------------------------------------- *)

let rec rewrite1 eqs t =
  match eqs with
    Atom(R("=",[l;r]))::oeqs ->
     (try tsubst (term_match undefined [l,t]) r
      with Failure _ -> rewrite1 oeqs t)
  | _ -> failwith "rewrite1";;

(* ------------------------------------------------------------------------- *)
(* Rewriting repeatedly and at depth (top-down).                             *)
(* ------------------------------------------------------------------------- *)

let rec rewrite eqs tm =
  try rewrite eqs (rewrite1 eqs tm) with Failure _ ->
  match tm with
    Var x -> tm
  | Fn(f,args) -> let tm' = Fn(f,map (rewrite eqs) args) in
                  if tm' = tm then tm else rewrite eqs tm';;

let%expect_test "eg: 3 * 2 + 4 in successor notation" =
  print_fol_formula
    (rewrite [{%fol|0 + x = x|}; {%fol|S(x) + y = S(x + y)|};
             {%fol|0 * x = 0|}; {%fol|S(x) * y = y + x * y|}]
            {%tm|S(S(S(0))) * S(S(0)) + S(S(S(S(0))))|});
  [%expect {| |}]
;;

(* ------------------------------------------------------------------------- *)
(* Note that ML doesn't accept nonlinear patterns.                           *)
(* ------------------------------------------------------------------------- *)

(*********** Point being that CAML doesn't accept nonlinear patterns

function (x,x) -> 0;;

 *********** Actually fun x x -> 0 works, but the xs seem to be
 *********** considered distinct
 **********)
