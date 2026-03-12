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

  let pairC = ContextualConversion.(!>>> ) Elpi.Builtin.pair
  let stringC = ContextualConversion.(!> ) BuiltInData.string

let json : Yojson.Basic.t Conversion.t = AlgebraicData.(declare {
  ty = Conversion.TyName "json";
  doc = "Yojson.Basic.t";
  pp = Yojson.Basic.pp;
  constructors = [
    K("json.null","",N,B `Null,M (fun ~ok ~ko -> function `Null -> ok | _ -> ko ()));
    K("json.bool","",A(Elpi.Builtin.bool,N),B (function x -> `Bool x),M (fun ~ok ~ko -> function `Bool x -> ok x | _ -> ko ()));
    K("json.int","",A(BuiltInData.int,N),B (function x -> `Int x),M (fun ~ok ~ko -> function `Int x -> ok x | _ -> ko ()));
    K("json.float","",A(BuiltInData.float,N),B (function x -> `Float x),M (fun ~ok ~ko -> function `Float x -> ok x | _ -> ko ()));
    K("json.string","",A(BuiltInData.string,N),B (function x -> `String x),M (fun ~ok ~ko -> function `String x -> ok x | _ -> ko ()));
    K("json.assoc","key value pairs. When generated from built-in predicates, keys are sorted",C((fun x -> listC (pairC stringC x)),N),
      B (function x -> `Assoc x),
      M (fun ~ok ~ko -> function `Assoc x ->
        let sx = List.stable_sort (fun (x,_) (y,_) -> String.compare x y) x in
        ok sx | _ -> ko ()));
    K("json.list","",C(listC,N),B (function x -> `List x),M (fun ~ok ~ko -> function `List x -> ok x | _ -> ko ()));
  ];
}
) |> ContextualConversion.(!<)

open BuiltIn
open BuiltInPredicate
open BuiltInPredicate.Notation
open BuiltInData
open Elpi.Builtin
let json_from_file = MLCode(Pred("json.from_file",
  In(string,"File",
  Out(json,"J",
  Out(diagnostic,"D",
  Easy {|like Yojson.Basic.from_file reads J from File.
If D is error then J is not assigned.|}))),
  (fun f _ _ ~depth ->
    try !: (Yojson.Basic.from_file ~fname:f f) +! mkOK
    with Yojson.Json_error s | Sys_error s -> ?: None +! (mkERROR s)
  )),DocAbove)

let json_from_string = MLCode(Pred("json.from_string",
  In(string,"String",
  Out(json,"J",
  Out(diagnostic,"D",
  Easy {|like Yojson.Basic.from_string reads J from String.
If D is error then J is not assigned.|}))),
  (fun f _ _ ~depth ->
    try !: (Yojson.Basic.from_string f) +! mkOK
    with Yojson.Json_error s -> ?: None +! (mkERROR s)
  )),DocAbove)

let json_to_file = MLCode(Pred("json.to_file",
  In(string,"File",
  In(json,"J",
  Out(diagnostic,"D",
  Easy {|like Yojson.Basic.to_file write J to File.|}))),
  (fun f j _ ~depth ->
    try Yojson.Basic.to_file f j; !: mkOK
    with Yojson.Json_error s | Sys_error s -> !: (mkERROR s)
  )),DocAbove)

let json_to_string = MLCode(Pred("json.to_string",
  In(json,"J",
  Out(string,"S",
  Out(diagnostic,"D",
  Easy {|like Yojson.Basic.to_string write J to a compact string S.|}))),
  (fun j _ _ ~depth ->
    try !: (Yojson.Basic.to_string ~std:true j) +! mkOK
    with Yojson.Json_error s -> ?: None +! (mkERROR s)
  )),DocAbove)

let json_to_string_pretty = MLCode(Pred("json.pretty_to_string",
  In(json,"J",
  Out(string,"S",
  Out(diagnostic,"D",
  Easy {|like Yojson.Basic.pretty_to_string write J to a nice string S.|}))),
  (fun j _ _ ~depth ->
    try !: (Yojson.Basic.pretty_to_string ~std:true j) +! mkOK
    with Yojson.Json_error s -> ?: None +! (mkERROR s)
  )),DocAbove)

let builtins =
  declare ~file_name:"json.elpi" [
    LPDoc {|Yojson bindings for Elpi|};
    LPDoc {|license: GNU Lesser General Public License Version 2.1 or later|};
    LPDoc {|------------------------------------------------------------------------|};
    LPDoc {|This code is not Rocq specific, i.e. could go to an Elpi specific package.|};
    MLData json;
    json_from_file;
    json_from_string;
    json_to_file;
    json_to_string;
    json_to_string_pretty;
    LPDoc {|------------------------------------------------------------------------|};
    LPDoc {|Rocq-Elpi APIs|};
    LPDoc {|------------------------------------------------------------------------|};
    LPCode {|
func coq.json->string json -> string.
coq.json->string J S :- json.pretty_to_string J S ok.

func coq.string->json string -> json.
coq.string->json S J :- json.from_string S J ok.

% [coq.extra-dep->json Dep J D] reads a json file declared as an extra
% dependency, see the coq.extra-dep API.
func coq.extra-dep->json string -> json, diagnostic.
coq.extra-dep->json S J D :- coq.extra-dep S (some P), !, json.from_file P J D.
coq.extra-dep->json S _ (error Msg) :- Msg is "unknown Extra Dependency " ^ S.

|}
  ]
