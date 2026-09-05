(* ========================================================================= *)
(* Initialize theorem proving example code.                                  *)
(*                                                                           *)
(* Copyright (c) 2003-2007, John Harrison. (See "LICENSE.txt" for details.)  *)
(* ========================================================================= *)

(* Run "dune build @lib/top" before starting the toplevel: everything
   loaded below is a build artifact. *)

Sys.interactive := false;;

#use "topfind";;
#require "num";;
#require "str";;

(* Quotation syntax.  This replaces the camlp5 setup: {%fml|p ==> q|} and
   {%tm|x + y|} expand to default_parser / secondary_parser calls. *)
#ppx "_build/default/ppx/driver/ppx_atp_driver.exe --as-ppx";;

(* .atp.objs/byte is where dune puts the .cmi, which the toplevel needs on
   its include path in addition to loading the .cma itself. *)
#directory "_build/default/lib/.atp.objs/byte";;
#load "_build/default/lib/atp.cma";;
open Atp_batch;;

#use "_build/default/lib/printers.ml";;

#use "inittop.ml";;

Sys.interactive := true;;
