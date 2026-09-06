open Lib

(* Warnings the book's style trips in this file; the rest of the
   library compiles with them on.  See lib/dune. *)
[@@@warning "-32"]

(* ========================================================================= *)
(* Simple algebraic expression example from the introductory chapter.        *)
(*                                                                           *)
(* Copyright (c) 2003-2007, John Harrison. (See "LICENSE.txt" for details.)  *)
(* ========================================================================= *)

type expression =
   Var of string
 | Const of int
 | Add of expression * expression
 | Mul of expression * expression;;

(* This chapter builds up to print_exp at the end, so the examples before it
   have nothing to print with.  The toplevel showed the constructor tree there;
   this does the same. *)
let rec dump_exp e =
  match e with
    Var s -> print_string ("Var \"" ^ s ^ "\"")
  | Const n -> print_string ("Const " ^ string_of_int n)
  | Add(e1,e2) ->
        print_string "Add("; dump_exp e1; print_string ","; dump_exp e2;
        print_string ")"
  | Mul(e1,e2) ->
        print_string "Mul("; dump_exp e1; print_string ","; dump_exp e2;
        print_string ")";;

(* ------------------------------------------------------------------------- *)
(* Trivial example of using the type constructors.                           *)
(* ------------------------------------------------------------------------- *)


let%expect_test "eg: Trivial example of using the type constructors" =
  dump_exp
    (Add(Mul(Const 2,Var "x"),Var "y"));
  [%expect {| Add(Mul(Const 2,Var "x"),Var "y") |}]
;;

(* ------------------------------------------------------------------------- *)
(* Simplification example.                                                   *)
(* ------------------------------------------------------------------------- *)

let simplify1 expr =
  match expr with
    Add(Const(m),Const(n)) -> Const(m + n)
  | Mul(Const(m),Const(n)) -> Const(m * n)
  | Add(Const(0),x) -> x
  | Add(x,Const(0)) -> x
  | Mul(Const(0),x) -> Const(0)
  | Mul(x,Const(0)) -> Const(0)
  | Mul(Const(1),x) -> x
  | Mul(x,Const(1)) -> x
  | _ -> expr;;

let rec simplify expr =
  match expr with
    Add(e1,e2) -> simplify1(Add(simplify e1,simplify e2))
  | Mul(e1,e2) -> simplify1(Mul(simplify e1,simplify e2))
  | _ -> simplify1 expr;;

let%expect_test "eg" =
  let e = Add(Mul(Add(Mul(Const(0),Var "x"),Const(1)),Const(3)),
              Const(12)) in
  dump_exp
    (e);
  dump_exp
    (simplify e);
  [%expect {| Add(Mul(Add(Mul(Const 0,Var "x"),Const 1),Const 3),Const 12)Const 15 |}]
;;


(* ------------------------------------------------------------------------- *)
(* Lexical analysis.                                                         *)
(* ------------------------------------------------------------------------- *)

let matches s = let chars = explode s in fun c -> mem c chars;;

let space = matches " \t\n\r"
and punctuation = matches "()[]{},"
and symbolic = matches "~`!@#$%^&*-+=|\\:;<>.?/"
and numeric = matches "0123456789"
and alphanumeric = matches
  "abcdefghijklmnopqrstuvwxyz_'ABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789";;

let rec lexwhile prop inp =
  match inp with
    c::cs when prop c -> let tok,rest = lexwhile prop cs in c^tok,rest
  | _ -> "",inp;;

let rec lex inp =
  match snd(lexwhile space inp) with
    [] -> []
  | c::cs -> let prop = if alphanumeric(c) then alphanumeric
                        else if symbolic(c) then symbolic
                        else fun c -> false in
             let toktl,rest = lexwhile prop cs in
             (c^toktl)::lex rest;;

let%expect_test _ =
  print_list print_quoted
    (lex(explode "2*((var_1 + x') + 11)"));
  print_list print_quoted
    (lex(explode "if (*p1-- == *p2++) then f() else g()"));
  [%expect {| ["2"; "*"; "("; "("; "var_1"; "+"; "x'"; ")"; "+"; "11"; ")"]["if"; "("; "*"; "p1"; "--"; "=="; "*"; "p2"; "++"; ")"; "then"; "f"; "("; ")"; "else"; "g"; "("; ")"] |}]
;;


(* ------------------------------------------------------------------------- *)
(* Parsing.                                                                  *)
(* ------------------------------------------------------------------------- *)

let rec parse_expression i =
  match parse_product i with
    e1,"+"::i1 -> let e2,i2 = parse_expression i1 in Add(e1,e2),i2
  | e1,i1 -> e1,i1

and parse_product i =
  match parse_atom i with
    e1,"*"::i1 -> let e2,i2 = parse_product i1 in Mul(e1,e2),i2
  | e1,i1 -> e1,i1

and parse_atom i =
  match i with
    [] -> failwith "Expected an expression at end of input"
  | "("::i1 -> (match parse_expression i1 with
                  e2,")"::i2 -> e2,i2
                | _ -> failwith "Expected closing bracket")
  | tok::i1 -> if forall numeric (explode tok)
               then Const(int_of_string tok),i1
               else Var(tok),i1;;

(* ------------------------------------------------------------------------- *)
(* Generic function to impose lexing and exhaustion checking on a parser.    *)
(* ------------------------------------------------------------------------- *)

let make_parser pfn s =
  let expr,rest = pfn (lex(explode s)) in
  if rest = [] then expr else failwith "Unparsed input";;

(* ------------------------------------------------------------------------- *)
(* Our parser.                                                               *)
(* ------------------------------------------------------------------------- *)

let parse_expr = make_parser parse_expression;;

let%expect_test _ =
  dump_exp
    (parse_expr "x + 1");
  (* ------------------------------------------------------------------------- *)
  (* Demonstrate automatic installation.                                       *)
  (* ------------------------------------------------------------------------- *)
  [%expect {| Add(Var "x",Const 1) |}]
;;


(* ------------------------------------------------------------------------- *)
(* Conservatively bracketing first attempt at printer.                       *)
(* ------------------------------------------------------------------------- *)

let rec string_of_exp e =
  match e with
    Var s -> s
  | Const n -> string_of_int n
  | Add(e1,e2) -> "("^(string_of_exp e1)^" + "^(string_of_exp e2)^")"
  | Mul(e1,e2) -> "("^(string_of_exp e1)^" * "^(string_of_exp e2)^")";;

let%expect_test "eg: Examples" =
  print_quoted
    (string_of_exp {%expr|x + 3 * y|});
  [%expect {| "(x + (3 * y))" |}]
;;


(* ------------------------------------------------------------------------- *)
(* Somewhat better attempt.                                                  *)
(* ------------------------------------------------------------------------- *)

let rec string_of_exp pr e =
  match e with
    Var s -> s
  | Const n -> string_of_int n
  | Add(e1,e2) ->
        let s = (string_of_exp 3 e1)^" + "^(string_of_exp 2 e2) in
        if 2 < pr then "("^s^")" else s
  | Mul(e1,e2) ->
        let s = (string_of_exp 5 e1)^" * "^(string_of_exp 4 e2) in
        if 4 < pr then "("^s^")" else s;;

(* ------------------------------------------------------------------------- *)
(* Install it.                                                               *)
(* ------------------------------------------------------------------------- *)

let print_exp e = Format.print_string ("<<"^string_of_exp 0 e^">>");;


(* ------------------------------------------------------------------------- *)
(* Examples.                                                                 *)
(* ------------------------------------------------------------------------- *)


(* ------------------------------------------------------------------------- *)
(* Example shows the problem.                                                *)
(* ------------------------------------------------------------------------- *)
