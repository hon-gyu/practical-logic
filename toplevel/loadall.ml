(* ========================================================================= *)
(* Load the atp library into an OCaml toplevel.                              *)
(*                                                                           *)
(* Run "dune build" first, then from the repo root:  #use "toplevel/loadall.ml";;
   The repo's .ocamlinit does this automatically.                            *)
(* ========================================================================= *)

Sys.interactive := false;;

#use "topfind";;
#require "num";;
#require "str";;

(* Quotation syntax: {%expr|..|}, {%prop|..|}, {%fol|..|} and {%tm|..|}. *)
#ppx "_build/default/ppx/driver/ppx_atp_driver.exe --as-ppx";;

#directory "_build/default/lib/.atp.objs/byte";;
#load "_build/default/lib/atp.cma";;

open Atp;;
open Atp.All;;

Initialization.init ();;

(* Optional: pretty-print formulas as <<p ==> q>> rather than constructor
   trees.  Comment this out to see the raw representation. *)
#use "toplevel/printers.ml";;

if Findlib.is_recorded_package "utop" then
  if Sys.file_exists "toplevel/utop-prefs.ml" then
    ignore (Toploop.use_silently Format.std_formatter
              (Toploop.File "toplevel/utop-prefs.ml"));;

Sys.interactive := true;;
