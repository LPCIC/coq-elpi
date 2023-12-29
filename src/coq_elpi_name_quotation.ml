(* coq-elpi: Coq terms as the object language of elpi                        *)
(* license: GNU Lesser General Public License Version 2.1 or later           *)
(* ------------------------------------------------------------------------- *)

module API = Elpi.API
open Coq_elpi_utils
open Coq_elpi_HOAS
open Names

let to_name src =
    if src = "_" then in_elpi_name Name.Anonymous
    else in_elpi_name (Name.Name (Id.of_string src))

(* Install the quotation *)
let () =
  let f ~depth state _loc src = state, to_name src in
  API.Quotation.register_named_quotation ~descriptor:interp_quotations ~name:"name" f;
  API.Quotation.register_named_quotation ~descriptor:synterp_quotations ~name:"name" f

let () =
  let f state s =
    let src = String.sub s 1 (String.length s - 2) in
    state, to_name src in
  API.Quotation.declare_backtick ~descriptor:interp_quotations ~name:"Name.t" f;
  API.Quotation.declare_backtick ~descriptor:synterp_quotations ~name:"Name.t" f
