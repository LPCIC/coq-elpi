(* coq-elpi: Coq terms as the object language of elpi                        *)
(* license: GNU Lesser General Public License Version 2.1 or later           *)
(* ------------------------------------------------------------------------- *)

let err msg = CErrors.user_err ~hdr:"elpi" msg

module E = Elpi_API

let feedback_fmt_write, feedback_fmt_flush =
  let b = Buffer.create 2014 in
  Buffer.add_substring b,
  (fun () ->
     let s = Buffer.to_bytes b in
     let s =
       let len = Bytes.length s in
       if len > 0 && Bytes.get s (len - 1) = '\n'
       then Bytes.sub_string s 0 (len - 1)
       else Bytes.to_string s in
     Feedback.msg_info Pp.(str s);
     Buffer.clear b)

let () = E.Setup.set_error (fun s -> err Pp.(str s))
let () = E.Setup.set_anomaly (fun s -> err Pp.(str s))
let () = E.Setup.set_type_error (fun s -> err Pp.(str s))
let () = E.Setup.set_warn (fun s -> Feedback.msg_warning Pp.(str s))
let () = E.Setup.set_std_formatter (Format.make_formatter feedback_fmt_write feedback_fmt_flush)
let () = E.Setup.set_err_formatter (Format.make_formatter feedback_fmt_write feedback_fmt_flush)


let nYI s = err Pp.(str"Not Yet Implemented: " ++ str s)

let pp2string pp x =
  let b = Buffer.create 80 in
  let fmt = Format.formatter_of_buffer b in
  Format.fprintf fmt "%a%!" pp x;
  Buffer.contents b

module C = Constr

let safe_destApp t =
  match C.kind t with
  | C.App(hd,args) -> C.kind hd, args
  | x -> x, [||]

let mkGHole =
  CAst.make
    (Glob_term.GHole(Evar_kinds.InternalHole,Misctypes.IntroAnonymous,None))

let mkApp t l =
  match t, l with
  | E.Extend.Data.Const c, [] -> t
  | E.Extend.Data.Const c, x::xs -> E.Extend.Data.App(c,x,xs)
  | _ -> assert false

let string_split_on_char c s =
  let len = String.length s in
  let rec aux n x =
    if x = len then [String.sub s n (x-n)]
    else if s.[x] = c then String.sub s n (x-n) :: aux (x+1) (x+1)
    else aux n (x+1)
  in
    aux 0 0

