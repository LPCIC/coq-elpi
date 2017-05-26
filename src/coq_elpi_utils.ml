(* coq-elpi: Coq terms as the object language of elpi                        *)
(* license: GNU Lesser General Public License Version 2.1 or later           *)
(* ------------------------------------------------------------------------- *)

let err msg = CErrors.user_err ~hdr:"elpi" msg

let () = Elpi_API.set_error (fun s -> err Pp.(str s))
let () = Elpi_API.set_anomaly (fun s -> err Pp.(str s))
let () = Elpi_API.set_type_error (fun s -> err Pp.(str s))

let nYI s = err Pp.(str"Not Yet Implemented: " ++ str s)

open Elpi_API.Data
open Elpi_API.Runtime

let pp2string pp x =
  let b = Buffer.create 80 in
  let fmt = Format.formatter_of_buffer b in
  Format.fprintf fmt "%a%!" pp x;
  Buffer.contents b

let rec deref_head on_arg depth = function
    | UVar ({ contents = g }, from, args) when g != Constants.dummy ->
       deref_head on_arg depth (deref_uv ~from ~to_:depth args g)
    | AppUVar ({contents = t}, from, args) when t != Constants.dummy ->
       deref_head on_arg depth (deref_appuv ~from ~to_:depth args t)
    | App(c,x,xs) when not on_arg ->
        App(c,deref_head true depth x,List.map (deref_head true depth) xs)
    | x -> x

let kind ~depth x = deref_head false depth x


module C = Constr

let safe_destApp t =
  match C.kind t with
  | C.App(hd,args) -> C.kind hd, args
  | x -> x, [||]

let mkGHole =
  CAst.make
    (Glob_term.GHole(Evar_kinds.InternalHole,Misctypes.IntroAnonymous,None))

