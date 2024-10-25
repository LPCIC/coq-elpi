(* coq-elpi: Coq terms as the object language of elpi                        *)
(* license: GNU Lesser General Public License Version 2.1 or later           *)
(* ------------------------------------------------------------------------- *)

module API = Elpi.API
open Coq_elpi_utils
open Coq_elpi_HOAS
open Names

let to_name ~loc src =
    if src = "_" then in_elpiast_name ~loc Name.Anonymous
    else in_elpiast_name ~loc (Name.Name (Id.of_string src))

(* Install the quotation *)
let () =
  let f ~language state loc src = to_name ~loc src in
  let _ = API.Quotation.register_named_quotation ~descriptor:interp_quotations ~name:"name" f in
  let _ = API.Quotation.register_named_quotation ~descriptor:synterp_quotations ~name:"name" f in
  ()

let () =
  let f ~language state loc s =
    let src = String.sub s 1 (String.length s - 2) in
    to_name ~loc src in
  let _ = API.Quotation.declare_backtick ~descriptor:interp_quotations ~name:"Name.t" f in
  let _ = API.Quotation.declare_backtick ~descriptor:synterp_quotations ~name:"Name.t" f in
  ()
