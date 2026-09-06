(* Every module of the library in one flat namespace, in dependency order, so
   that "open Atp.All" reproduces the single namespace the concatenated
   atp_batch.ml used to provide.  Where two modules define the same name the
   later one wins, exactly as it did in the concatenation.  Convenience only:
   prefer opening the individual modules you need. *)

include Initialization
include Lib
include Intro
include Formulas
include Prop
include Propexamples
include Defcnf
include Dp
include Stal
include Bdd
include Fol
include Skolem
include Herbrand
include Unif
include Tableaux
include Resolution
include Prolog
include Meson
include Skolems
include Equal
include Cong
include Rewrite
include Order
include Completion
include Eqelim
include Paramodulation
include Decidable
include Qelim
include Cooper
include Complex
include Real
include Grobner
include Geom
include Interpolation
include Combining
include Lcf
include Lcfprop
include Folderived
include Lcffol
include Tactics
include Print_fpf
