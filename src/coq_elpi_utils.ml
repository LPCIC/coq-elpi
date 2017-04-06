(* coq-elpi: Coq terms as the object language of elpi                        *)
(* license: GNU Lesser General Public License Version 2.1 or later           *)
(* ------------------------------------------------------------------------- *)

let debug = Summary.ref ~name:"elpi-debug" false

let err msg = CErrors.user_err ~hdr:"elpi" msg

let nYI s = err Pp.(str"Not Yet Implemented: " ++ str s)

open Elpi_runtime

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
  Glob_term.GHole(Loc.ghost,Evar_kinds.InternalHole,Misctypes.IntroAnonymous,None)

