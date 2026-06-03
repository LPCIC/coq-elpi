module API = Elpi.API
module E = API.RawData

let declare = let open API.AlgebraicData in declare


type mysumT = | MyC : int -> mysumT | MyA : (mysumT * mysumT) -> mysumT

let rec compute (s : mysumT) = match s with
  | MyC n -> n
  | MyA (s1, s2) -> compute s1 + compute s2

let myC = E.Constants.declare_global_symbol "myC"
let myA = E.Constants.declare_global_symbol "myA"

let rec embed = function
  | MyC n -> E.mkApp myC (API.RawOpaqueData.of_int n) []
  | MyA (s1, s2) -> E.mkApp myA (embed s1) [embed s2]

let mysum_ = API.(AlgebraicData.declare {
  ty = TyName "mysumT";
  doc = "blibli";
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

let compute_api = API.BuiltIn.MLCode(Pred("compute",
    In(mysum_, "mysumT",
    Out(mysum_, "int",
    Easy("AAA"))),
    fun a _ ~depth -> (), Some (MyC (compute a))),
    DocAbove)

let builtins =
  API.BuiltIn.declare ~file_name:"ext.elpi" [
  MLData mysum_;
  compute_api
]
