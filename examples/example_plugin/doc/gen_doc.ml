(* the builtins are taken from the src folder, where the MyExtension_plugin library is defined
*)
let _ = Elpi.API.BuiltIn.document_file ~header:"% Generated"
  MyExtension_plugin.My_extension_ocaml_code.builtins
