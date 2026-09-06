open Lib
open Fol

(* ========================================================================= *)
(* Unification for first order terms.                                        *)
(*                                                                           *)
(* Copyright (c) 2003-2007, John Harrison. (See "LICENSE.txt" for details.)  *)
(* ========================================================================= *)

let rec istriv env x t =
  match t with
    Var y -> y = x || defined env y && istriv env x (apply env y)
  | Fn(f,args) -> exists (istriv env x) args && failwith "cyclic";;

(* ------------------------------------------------------------------------- *)
(* Main unification procedure                                                *)
(* ------------------------------------------------------------------------- *)

let rec unify env eqs =
  match eqs with
    [] -> env
  | (Fn(f,fargs),Fn(g,gargs))::oth ->
        if f = g && length fargs = length gargs
        then unify env (zip fargs gargs @ oth)
        else failwith "impossible unification"
  | (Var x,t)::oth | (t,Var x)::oth ->
        if defined env x then unify env ((apply env x,t)::oth)
        else unify (if istriv env x t then env else (x|->t) env) oth;;

(* ------------------------------------------------------------------------- *)
(* Solve to obtain a single instantiation.                                   *)
(* ------------------------------------------------------------------------- *)

let rec solve env =
  let env' = mapf (tsubst env) env in
  if env' = env then env else solve env';;

(* ------------------------------------------------------------------------- *)
(* Unification reaching a final solved form (often this isn't needed).       *)
(* ------------------------------------------------------------------------- *)

let fullunify eqs = solve (unify undefined eqs);;

(* ------------------------------------------------------------------------- *)
(* Examples.                                                                 *)
(* ------------------------------------------------------------------------- *)

let unify_and_apply eqs =
  let i = fullunify eqs in
  let apply (t1,t2) = tsubst i t1,tsubst i t2 in
  map apply eqs;;

let%expect_test _ =
  print_list (print_pair printert printert)
    (unify_and_apply [{%tm|f(x,g(y))|},{%tm|f(f(z),w)|}]);
  print_list (print_pair printert printert)
    (unify_and_apply [{%tm|f(x,y)|},{%tm|f(y,x)|}]);
  (****  unify_and_apply [{%tm|f(x,g(y))|},{%tm|f(y,x)|}];; *****)
  print_list (print_pair printert printert)
    (unify_and_apply [{%tm|x_0|},{%tm|f(x_1,x_1)|};
                     {%tm|x_1|},{%tm|f(x_2,x_2)|};
                     {%tm|x_2|},{%tm|f(x_3,x_3)|}]);
  let cyclic() = "cyclic" |=> parset "0" in
  print_graph print_quoted printert
    (fullunify [parset "x", parset "x"]);
  print_graph print_quoted printert
    (fullunify [parset "p(X,Y)", parset "p(Y,X)"]);
  (* Makes solve do some work. *)
  print_graph print_quoted printert
    (fullunify [parset "p(x,x)", parset "p(y,0)"]);
  print_graph print_quoted printert
    (try fullunify [parset "p(x,x)", parset "p(y,f(y))"]
    with Failure _ ->  cyclic());
  print_graph print_quoted printert
    (fullunify [parset "p(X,Y,2)", parset "p(Y,X,X)"]);
  print_graph print_quoted printert
    (try fullunify [parset "Q(a, x, f(x))", parset "Q(2, y, y)"]
    with Failure _ -> cyclic());
  print_graph print_quoted printert
    (fullunify [parset "Q(x, y, z)", parset "Q(u, h(v, v), u)"]);
  print_graph print_quoted printert
    (fullunify [parset "q(p(X,Y),p(Y,X))", parset "q(Z,Z)"]);
  (* This one gives "solve" some work to do. *)
  let expander = [
    (parset "x"),(parset "f(y,y)");
    (parset "y"),(parset "f(z,z)");
    (parset "z"),(parset "f(w,w)")] in
  print_list (print_pair printert printert)
    (expander);
  print_graph print_quoted printert
    (unify undefined expander);
  print_graph print_quoted printert
    (fullunify expander);
  [%expect {|
    [(<<|f(f(z),g(y))|>>, <<|f(f(z),g(y))|>>)][(<<|f(y,y)|>>, <<|f(y,y)|>>)][(
    <<|f(f(f(x_3,x_3),f(x_3,x_3)),f(f(x_3,x_3),f(x_3,x_3)))|>>, <<|f(f(f(
                                                                       x_3,x_3),
                                                                       f(
                                                                       x_3,x_3))
                                                                     ,
                                                                     f(f(
                                                                       x_3,x_3),
                                                                       f(
                                                                       x_3,x_3)))|>>); (
    <<|f(f(x_3,x_3),f(x_3,x_3))|>>, <<|f(f(x_3,x_3),f(x_3,x_3))|>>); (<<|
                                                                      f(x_3,x_3)|>>,
    <<|f(x_3,x_3)|>>)][][("X", <<|Y|>>)][("x", <<|0|>>); ("y", <<|0|>>)][("cyclic",
    <<|0|>>)][("X", <<|2|>>); ("Y", <<|2|>>)][("cyclic", <<|0|>>)][("x",
    <<|u|>>); ("y", <<|h(v,v)|>>); ("z", <<|u|>>)][("X", <<|Y|>>); ("Z",
    <<|p(Y,Y)|>>)][(<<|x|>>, <<|f(y,y)|>>); (<<|y|>>, <<|f(z,z)|>>); (<<|z|>>,
    <<|f(w,w)|>>)][("x", <<|f(y,y)|>>); ("y", <<|f(z,z)|>>); ("z", <<|f(w,w)|>>)][("x",
    <<|f(f(f(w,w),f(w,w)),f(f(w,w),f(w,w)))|>>); ("y", <<|f(f(w,w),f(w,w))|>>); ("z",
    <<|f(w,w)|>>)]
    |}]
;;
