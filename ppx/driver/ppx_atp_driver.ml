(* Standalone driver, so the quotation syntax also works in the toplevel:
   #ppx "_build/default/ppx/driver/ppx_atp_driver.exe --as-ppx";; *)
let () = Ppxlib.Driver.standalone ()
