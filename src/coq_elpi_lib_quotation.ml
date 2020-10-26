
(* coq-elpi: Coq terms as the object language of elpi                        *)
(* license: GNU Lesser General Public License Version 2.1 or later           *)
(* ------------------------------------------------------------------------- *)

module API = Elpi.API
module Q = API.Quotation

open Coq_elpi_HOAS

let coqlib_quotation ~depth state loc src =
  let src = CString.trim src in
  if Coqlib.has_ref src then
    let ref = Coqlib.lib_ref src in
    let state, t, _ = gref.API.Conversion.embed ~depth state ref in
    state, t
  else
    let loc = Coq_elpi_utils.to_coq_loc loc in
    CErrors.user_err ~loc ~hdr:"elpi" Pp.(str "No coqlib entry for " ++ str src)

let () = Q.register_named_quotation ~name:"lib" coqlib_quotation


