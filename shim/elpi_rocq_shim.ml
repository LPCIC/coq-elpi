(* elpi-rocq-shim: an approximation of the quotations of rocq-elpi, for
   checking Elpi programs outside Rocq (elpi-lsp, see elpi.toml).
   license: GNU Lesser General Public License Version 2.1 or later

   The text of a {{ ... }} is not parsed as Rocq syntax: only its
   antiquotations are, lp:X, lp:(F x) and lp:{{ ... }}, as Elpi terms (the
   Elpi quotation). The quotation is the term [rocq_quotation [A1, ..., An]]
   of the antiquotations A1 ... An, of type term: enough to type check the
   antiquotations and to resolve their names. A name of the Rocq text (e.g.
   bound by fun x => ...) that occurs in an antiquotation is bound around it,
   x\ (F x): the Rocq binders are not parsed. The other quotations of
   rocq-elpi ({{:gref ...}}, {{:name ...}}, `x`) are constants of their
   type. *)

open Elpi.API

let rocq_quotationc = RawData.Constants.declare_global_symbol "rocq_quotation"
let rocq_grefc = RawData.Constants.declare_global_symbol "rocq_gref"
let rocq_namec = RawData.Constants.declare_global_symbol "rocq_name"

let is_ident_char = function
  | 'a' .. 'z' | 'A' .. 'Z' | '0' .. '9' | '_' | '\'' -> true
  | _ -> false

(* the position after the "close" that closes the "open" at [i] (nested ones
   count), or the length of [s] if it is not closed *)
let closing s ~open_ ~close i =
  let n = String.length s and lo = String.length open_ and lc = String.length close in
  let at i w = i + String.length w <= n && String.equal (String.sub s i (String.length w)) w in
  let rec loop depth i =
    if i >= n then n
    else if at i close then (if depth = 1 then i + lc else loop (depth - 1) (i + lc))
    else if at i open_ then loop (depth + 1) (i + lo)
    else loop depth (i + 1) in
  loop 1 (i + lo)

(* the identifiers of [s], each once *)
let identifiers s =
  let n = String.length s in
  let rec loop acc i =
    if i >= n then List.rev acc
    else if is_ident_char s.[i] && (i = 0 || not (is_ident_char s.[i - 1])) then
      let j = ref i in
      while !j < n && (is_ident_char s.[!j] || s.[!j] = '.') do incr j done;
      let id = String.sub s i (!j - i) in
      loop (if List.exists (String.equal id) acc then acc else id :: acc) !j
    else loop acc (i + 1) in
  loop [] 0

(* the antiquotations of [s], with the offset of their Elpi text:
   lp:X, lp:(F x) (the text with its parentheses), lp:{{ ... }} (the text
   inside the braces) *)
let antiquotations s =
  let n = String.length s in
  let rec loop acc i =
    if i + 3 > n then List.rev acc
    else if String.equal (String.sub s i 3) "lp:" && (i = 0 || not (is_ident_char s.[i - 1])) then
      let j = i + 3 in
      if j + 1 < n && s.[j] = '{' && s.[j + 1] = '{' then
        let k = closing s ~open_:"{{" ~close:"}}" j in
        let stop = if k >= 2 && k <= n && k > j + 2 then k - 2 else k in
        loop ((j + 2, String.sub s (j + 2) (max 0 (stop - j - 2))) :: acc) k
      else if j < n && s.[j] = '(' then
        let k = closing s ~open_:"(" ~close:")" j in
        loop ((j, String.sub s j (k - j)) :: acc) k
      else
        let k = ref j in
        while !k < n && is_ident_char s.[!k] do incr k done;
        if !k = j then loop acc j else loop ((j, String.sub s j (!k - j)) :: acc) !k
    else loop acc (i + 1) in
  loop [] 0

(* the location of the text of [s] at [off], [loc] being the one of [s] *)
let loc_at (loc : Ast.Loc.t) s off len =
  let line = ref loc.line and line_starts_at = ref loc.line_starts_at in
  String.iteri (fun i c -> if i < off && c = '\n' then (incr line; line_starts_at := loc.source_start + i + 1)) s;
  { loc with line = !line; line_starts_at = !line_starts_at;
    source_start = loc.source_start + off; source_stop = loc.source_start + off + len }

(* [s] without its antiquotations: the Rocq text *)
let rocq_text s aqs =
  let b = Bytes.of_string s in
  List.iter (fun (off, text) -> Bytes.fill b off (String.length text) ' ') aqs;
  Bytes.to_string b

(* a Rocq name: an identifier that starts with a letter, not lp *)
let is_rocq_name x =
  match x.[0] with
  | 'a' .. 'z' | 'A' .. 'Z' -> not (String.equal x "lp") && not (String.contains x '.')
  | _ -> false

let rocq_quotation ~language:_ state loc s =
  let aqs = antiquotations s in
  let names = List.filter is_rocq_name (identifiers (rocq_text s aqs)) in
  let args = aqs |> List.map (fun (off, text) ->
    let bound = List.filter (fun x -> List.exists (String.equal x) (identifiers text)) names in
    let prefix = String.concat "" (List.map (fun x -> x ^ "\\ ") bound) in
    (* the location of the text, the prefix and the parenthesis before it *)
    let l = loc_at loc s off (String.length text) in
    let l = { l with source_start = l.source_start - String.length prefix - 1 } in
    Quotation.elpi ~language:Quotation.elpi_language state l (prefix ^ "(" ^ text ^ ")")) in
  (* each one of type any, so that the list can mix types *)
  let any t = Ast.Term.mkCast ~loc t { Ast.Type.it = Ast.Type.Any; loc } in
  let list = List.fold_right (fun t acc -> Ast.Term.mkCons ~loc ~hdloc:loc (any t) acc) args (Ast.Term.mkNil ~loc) in
  Ast.Term.mkAppGlobal ~loc ~hdloc:loc rocq_quotationc list []

let constant c ~language:_ _state loc _s = Ast.Term.mkGlobal ~loc c

let () =
  Quotation.set_default_quotation rocq_quotation;
  List.iter (fun name -> ignore (Quotation.register_named_quotation ~name rocq_quotation)) ["coq"; "pat"];
  ignore (Quotation.register_named_quotation ~name:"gref" (constant rocq_grefc));
  ignore (Quotation.register_named_quotation ~name:"name" (constant rocq_namec));
  ignore (Quotation.declare_backtick ~name:"Name.t" (constant rocq_namec))

let builtins : Setup.builtins = Plugin.register ~name:"rocq-shim" [
    BuiltIn.LPDoc "The quotations of rocq-elpi, approximated (the plugin rocq-shim of findlib package elpi-rocq-shim): the type checker only sees the antiquotations of a {{ ... }}";
    (* coq-builtin.elpi uses the quotations too: its types are declared here,
       the plugin comes first in the prelude *)
    BuiltIn.LPCode "data term.";
    BuiltIn.LPCode "data gref.";
    BuiltIn.LPCode "data name.";
    BuiltIn.LPCode "symb rocq_quotation : list any -> term.";
    BuiltIn.LPCode "symb rocq_gref : gref.";
    BuiltIn.LPCode "symb rocq_name : name.";
    BuiltIn.MLConstants [rocq_quotationc; rocq_grefc; rocq_namec];
  ]
