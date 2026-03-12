open Elpi.API

(* todo, move this in Elpi, there are already two copies of this code
in rocq-elpi *)
let listC (d : ('a,'h,'cst) ContextualConversion.t) =
  let embed ~depth h cst s l =
    let s, l, eg = Utils.map_acc (d.ContextualConversion.embed ~depth h cst ) s l in
    s, Utils.list_to_lp_list l, eg in
  let readback ~depth h cst s t =
    Utils.map_acc (d.ContextualConversion.readback ~depth h cst) s
      (Utils.lp_list_to_list ~depth t)
  in
  let pp fmt l =
    Format.fprintf fmt "[%a]" (RawPp.list d.ContextualConversion.pp ~boxed:true "; ") l in
  { ContextualConversion.embed; readback;
    ty = TyApp ("list",d.ContextualConversion.ty,[]);
    pp;
    pp_doc = (fun fmt () -> ()) }


open BuiltInData
open Elpi.Builtin

let xml : Xml.xml Conversion.t = AlgebraicData.(declare {
  ty = Conversion.TyName "xml";
  doc = "Xml.xml";
  pp = (fun fmt x -> Format.fprintf fmt "%s" (Xml.to_string_fmt x));
  constructors = [
    K("xml.element","Attributes are sorted by key",A(string,A(list (pair string string),C(listC,N))),
      B (fun tag attrs bo -> Element(tag,attrs,bo)),
      M (fun ~ok ~ko -> function Element(t,a,b) ->
        let a = List.stable_sort (fun (x,_) (y,_) -> String.compare x y) a in
        ok t a b | _ -> ko ()));
    K("xml.pcdata","",A(string,N),B (fun x -> PCData x),M (fun ~ok ~ko -> function Xml.PCData s -> ok s | _ -> ko ()));
  ];
}
) |> ContextualConversion.(!<)

open BuiltIn
open BuiltInPredicate
open BuiltInPredicate.Notation
let xml_parse_file = MLCode(Pred("xml.parse_file",
  In(string,"File",
  Out(xml,"XML",
  Out(diagnostic,"D",
  Easy {|like Xml.parse_file reads XML from File.
If D is error then XML is not assigned.|}))),
  (fun f _ _ ~depth ->
    try !: (Xml.parse_file f) +! mkOK
    with
    | Xml.Error e -> ?: None +! (mkERROR (Xml.error e))
    | Xml.File_not_found s | Xml_light_errors.File_not_found s -> ?: None +! (mkERROR s)
  )),DocAbove)

let xml_parse_string = MLCode(Pred("xml.parse_string",
  In(string,"String",
  Out(xml,"XML",
  Out(diagnostic,"D",
  Easy {|like Xml.parse_string reads XML from String.
If D is error then XML is not assigned.|}))),
  (fun f _ _ ~depth ->
    try !: (Xml.parse_string f) +! mkOK
    with Xml.Error e | Xml_light_errors.Xml_error e -> ?: None +! (mkERROR (Xml.error e))
  )),DocAbove)

let xml_to_string = MLCode(Pred("xml.to_string",
  In(xml,"XML",
  Out(string,"S",
  Out(diagnostic,"D",
  Easy {|like Xml.to_string write XML to a compact string S.|}))),
  (fun j _ _ ~depth ->
    !: (Xml.to_string j) +! mkOK
  )),DocAbove)

let xml_to_string_fmt = MLCode(Pred("xml.to_string_fmt",
  In(xml,"XML",
  Out(string,"S",
  Out(diagnostic,"D",
  Easy {|like Xml.to_string_fmt write XML to a nice string S.|}))),
  (fun j _ _ ~depth ->
    !: (Xml.to_string_fmt j) +! mkOK
  )),DocAbove)

let builtins =
  declare ~file_name:"xml.elpi" [
    LPDoc {|Xml-light bindings for Elpi|};
    LPDoc {|license: GNU Lesser General Public License Version 2.1 or later|};
    LPDoc {|------------------------------------------------------------------------|};
    LPDoc {|This code is not Rocq specific, i.e. could go to an Elpi specific package.|};
    MLData xml;
    xml_parse_file;
    xml_parse_string;
    xml_to_string;
    xml_to_string_fmt;
    LPDoc {|------------------------------------------------------------------------|};
    LPDoc {|Rocq-Elpi APIs|};
    LPDoc {|------------------------------------------------------------------------|};
    LPCode {|
func coq.xml->string xml -> string.
coq.xml->string XML S :- xml.to_string_fmt XML S ok.

func coq.string->xml string -> xml.
coq.string->xml S XML :- xml.parse_string S XML ok.

% [coq.extra-dep->xml Dep XML D] reads a xml file declared as an extra
% dependency, see the coq.extra-dep API.
func coq.extra-dep->xml string -> xml, diagnostic.
coq.extra-dep->xml S XML D :- coq.extra-dep S (some P), !, xml.parse_file P XML D.
coq.extra-dep->xml S _ (error Msg) :- Msg is "unknown Extra Dependency " ^ S.

|}
  ]
