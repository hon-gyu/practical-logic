(* ========================================================================= *)
(* Quotation syntax for Harrison's formulas and terms.                       *)
(*                                                                           *)
(* Replaces the camlp5 quotation expander in Quotexpander.ml.  camlp5        *)
(* rewrote the book's <<...>> notation, which plain OCaml cannot parse at    *)
(* all; a ppx works on an already-parsed tree, so the notation becomes a     *)
(* quoted-string extension instead:                                          *)
(*                                                                           *)
(*   {%fml|p ==> q /\ ~r|}   ->  default_parser "p ==> q /\ ~r"              *)
(*   {%tm|x + y|}            ->  secondary_parser "x + y"                    *)
(*                                                                           *)
(* {|...|} needs no escaping, so the /\ and \/ connectives are written       *)
(* exactly as in the book.                                                   *)
(* ========================================================================= *)

open Ppxlib

(* The parser is named but deliberately left unresolved, so that the         *)
(* progressive shadowing of default_parser through intro.ml, prop.ml and     *)
(* fol.ml still selects the right parser at each use site, exactly as the    *)
(* camlp5 expansion did.                                                     *)
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
      [ extension "fml" "default_parser"; extension "tm" "secondary_parser" ]
