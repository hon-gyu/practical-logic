(* Optional: toplevel printers, so the REPL shows a formula as
   <<p ==> q>> rather than its constructor tree.  #install_printer is a
   toplevel directive, so these cannot live in the compiled library.
   Loaded by toplevel/loadall.ml. *)

#install_printer Atp.Initialization.print_num;;
#install_printer Atp.Lib.print_fpf;;
#install_printer Atp.Intro.print_exp;;
#install_printer Atp.Prop.print_prop_formula;;
#install_printer Atp.Bdd.print_bdd;;
#install_printer Atp.Fol.printert;;
#install_printer Atp.Fol.print_fol_formula;;
#install_printer Atp.Lcf.print_thm;;
#install_printer Atp.Tactics.print_goal;;
#install_printer Atp.Print_fpf.print_func;;
