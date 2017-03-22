DECLARE PLUGIN "elpi"

open Stdarg

VERNAC COMMAND EXTEND Elpi CLASSIFIED AS SIDEFF
| [ "Elpi" "Run" string(s) ] -> [ Coq_elpi.exec s ]
| [ "Elpi" "Path" string(s) ] -> [ Coq_elpi.path s ]
| [ "Elpi" "Load" "File" string(s) ] -> [ Coq_elpi.load_file s ]
(* | [ "Elpi" "Load" string(s) ] -> [ Coq_elpi.load_string s ] *)
END
