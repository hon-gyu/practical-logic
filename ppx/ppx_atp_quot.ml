(* ========================================================================= *)
(* Quotation syntax for Harrison's formulas and terms.                       *)
(*                                                                           *)
(* Replaces the camlp5 quotation expander in Quotexpander.ml.  camlp5        *)
(* rewrote the book's <<...>> notation, which plain OCaml cannot parse at    *)
(* all; a ppx works on an already-parsed tree, so the notation becomes a     *)
(* quoted-string extension instead:                                          *)
(*                                                                           *)
(*   {%expr|2 * x + y|}       ->  parse_expr "2 * x + y"                     *)
(*   {%prop|p ==> q /\ ~r|}   ->  parse_prop_formula "p ==> q /\ ~r"         *)
(*   {%fol|forall x. P(x)|}   ->  parse_fol_formula "forall x. P(x)"         *)
(*   {%tm|x + y|}             ->  parset "x + y"                             *)
(*                                                                           *)
(* {|...|} needs no escaping, so the /\ and \/ connectives are written       *)
(* exactly as in the book.                                                   *)
(*                                                                           *)
(* camlp5 had a single <<...>> that meant whichever default_parser was in    *)
(* scope, which is why the book's sources redefine default_parser in         *)
(* intro.ml, prop.ml and fol.ml.  Naming the level explicitly removes that   *)
(* dependence on definition order, which is what lets the sources be         *)
(* ordinary modules rather than one concatenated file.                       *)
(* ========================================================================= *)

open Ppxlib

(* The parser is named but left unqualified, so each quotation resolves to
   whatever the using module has in scope - normally the one this library
   defines, but a module may shadow it. *)
let expand parser_name ~ctxt s =
  let loc = Expansion_context.Extension.extension_point_loc ctxt in
  let open Ast_builder.Default in
  eapply ~loc (evar ~loc parser_name) [ estring ~loc s ]

let extension name parser_name =
  Extension.V3.declare name Extension.Context.expression
    Ast_pattern.(single_expr_payload (estring __))
    (expand parser_name)

let () =
  Driver.register_transformation "atp_quot"
    ~extensions:
      [ extension "expr" "parse_expr";
        extension "prop" "parse_prop_formula";
        extension "fol" "parse_fol_formula";
        extension "tm" "parset" ]
