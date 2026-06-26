(* the builtins are taken from the src folder
   this folder is a library called Ext_plug.
   From ths Ext module we get the builtins constant
*)
let _ = Elpi.API.BuiltIn.document_file ~header:"% Generated"
  Ext_plug.New_api.builtins
