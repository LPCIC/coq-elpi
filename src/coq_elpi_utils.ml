(* coq-elpi: Coq terms as the object language of elpi                        *)
(* license: GNU Lesser General Public License Version 2.1 or later           *)
(* ------------------------------------------------------------------------- *)

let err msg = CErrors.user_err ~hdr:"elpi" msg

module E = Elpi_API

let () = E.Setup.set_error (fun s -> err Pp.(str s))
let () = E.Setup.set_anomaly (fun s -> err Pp.(str s))
let () = E.Setup.set_type_error (fun s -> err Pp.(str s))

let nYI s = err Pp.(str"Not Yet Implemented: " ++ str s)

let pp2string pp x =
  let b = Buffer.create 80 in
  let fmt = Format.formatter_of_buffer b in
  Format.fprintf fmt "%a%!" pp x;
  Buffer.contents b

let kind = E.Extend.Utils.deref_head

module C = Constr

let safe_destApp t =
  match C.kind t with
  | C.App(hd,args) -> C.kind hd, args
  | x -> x, [||]

let mkGHole =
  CAst.make
    (Glob_term.GHole(Evar_kinds.InternalHole,Misctypes.IntroAnonymous,None))

