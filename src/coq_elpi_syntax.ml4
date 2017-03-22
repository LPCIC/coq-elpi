DECLARE PLUGIN "elpi"

open Stdarg

VERNAC COMMAND EXTEND Elpi CLASSIFIED AS SIDEFF
| [ "Elpi" "Run" string(s) ] -> [ Coq_elpi.exec s ]
| [ "Elpi" "Init" string_list(s) ] -> [ Coq_elpi.init s ]
| [ "Elpi" "Accumulate" "File" string_list(s) ] -> [ Coq_elpi.load_files s ]
| [ "Elpi" "Accumulate" "Files" string_list(s) ] -> [ Coq_elpi.load_files s ]
| [ "Elpi" "Accumulate" string(s) ] -> [ Coq_elpi.load_string s ]
(* | [ "Elpi" "Load" string(s) ] -> [ Coq_elpi.load_string s ] *)
END
