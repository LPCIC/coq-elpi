module API = Elpi.API
module E = API.RawData

(* defining a ad-hoc type in caml *)
type mysumT = | MyC : int -> mysumT | MyA : (mysumT * mysumT) -> mysumT

let rec compute (s : mysumT) = match s with
  | MyC n -> n
  | MyA (s1, s2) -> compute s1 + compute s2

(* declaring the elpi symbol corresponding to the constructors of mysumT *)
let myC = E.Constants.declare_global_symbol "myC"
let myA = E.Constants.declare_global_symbol "myA"

(* declaring the caml type mysumT in elpi *)
let mysum_ = API.(AlgebraicData.declare {
  ty = TyName "mysumT";
  doc = "description for the new elpi type";
  pp = (fun fmt _ -> Format.fprintf fmt "<todo>");
  constructors = [
   K("myC","",A(BuiltInData.int, N),
     B (fun x -> MyC x),
     M (fun ~ok ~ko  t -> match t with MyC n -> ok n | _ -> ko ()));
   K("myA","",S(S(N)),
     B (fun x y -> MyA (x, y)),
     M (fun ~ok ~ko t -> match t with MyA (x,y) -> ok x y | _ -> ko ()))
]
} |> ContextualConversion.(!<))

(* declaring a new elpi API *)
let compute_api = API.BuiltIn.MLCode(Pred("compute",
    In(mysum_, "mysumT",
    Out(mysum_, "int",
    Easy("Description for the new API"))),
    (* The implementation of the API is the result of compute *)
    fun a _ ~depth:_ -> (), Some (MyC (compute a))),
    DocAbove)

(* we declare the neame of the file in which the new API are declared
   and what are the new elpi object defined *)
let builtins =
  API.BuiltIn.declare ~file_name:"ext.elpi" [
  MLData mysum_;
  compute_api
]
