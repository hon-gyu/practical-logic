(* ========================================================================= *)
(* Tweak OCaml default state ready for theorem proving code.                 *)
(*                                                                           *)
(* Copyright (c) 2003-2007, John Harrison. (See "LICENSE.txt" for details.)  *)
(* ========================================================================= *)

(* These used to run when the concatenated source was loaded.  As a module of
   a library nothing forces them, so they are an explicit call: run "init ()"
   once at the start of any program or toplevel session.  Deep proof search
   overflows the default stack without it. *)
let init () =
  Gc.set { (Gc.get ()) with Gc.stack_limit = 16777216 };  (* Up the stack size *)
  Format.set_margin 72                                    (* Reduce margins    *)

(* Num, Format and Str were opened here for every file that followed; the
   library now does that with -open flags in lib/dune. *)

let print_num n = Format.print_string (Num.string_of_num n)  (* Avoid range limit *)
