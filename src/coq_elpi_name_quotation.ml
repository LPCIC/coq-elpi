(* coq-elpi: Coq terms as the object language of elpi                        *)
(* license: GNU Lesser General Public License Version 2.1 or later           *)
(* ------------------------------------------------------------------------- *)

module EC = Elpi_API.Extend.Compile
open Coq_elpi_HOAS
open Names

let to_name src =
    if src = "_" then in_elpi_name Name.Anonymous
    else in_elpi_name (Name.Name (Id.of_string src))

(* Install the quotation *)
let () = EC.register_named_quotation ~name:"name"
  (fun ~depth state src -> state, to_name src)
;;

let () = Elpi_API.Extend.CustomFunctor.declare_backtick ~name:"Name.t"
  (fun state s ->
     let src = String.sub s 1 (String.length s - 2) in
     state, to_name src)
