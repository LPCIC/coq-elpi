(* coq-elpi: Coq terms as the object language of elpi                        *)
(* license: GNU Lesser General Public License Version 2.1 or later           *)
(* ------------------------------------------------------------------------- *)

module E = Elpi_API
open Coq_elpi_HOAS
open Names

let to_name src =
    if src = "_" then in_elpi_name Name.Anonymous
    else in_elpi_name (Name.Name (Id.of_string src))

(* Install the quotation *)
let () = E.Quotation.register_named_quotation ~name:"name"
  (fun ~depth state _loc src -> state, to_name src)
;;

let () = E.Quotation.declare_backtick ~name:"Name.t"
  (fun state s ->
     let src = String.sub s 1 (String.length s - 2) in
     state, to_name src)
