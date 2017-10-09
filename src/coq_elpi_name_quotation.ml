(* coq-elpi: Coq terms as the object language of elpi                        *)
(* license: GNU Lesser General Public License Version 2.1 or later           *)
(* ------------------------------------------------------------------------- *)

module EC = Elpi_API.Extend.Compile
open Coq_elpi_HOAS
open Names

(* Install the quotation *)
let () = EC.register_named_quotation "name" (fun ~depth state src ->
  state,
    if src = "_" then in_elpi_name Name.Anonymous
    else in_elpi_name (Name.Name (Id.of_string src))
  )
;;
