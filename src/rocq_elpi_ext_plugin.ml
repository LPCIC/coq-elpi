module API = Elpi.API
module E = API.RawData

let declare = let open API.AlgebraicData in declare


type mynatT = | Myzero : mynatT | MyS : mynatT -> mynatT
let myzeroc = E.Constants.declare_global_symbol "myzero"
let mysc = E.Constants.declare_global_symbol "mysucc"

let rec embed = function
  | Myzero -> E.mkConst myzeroc
  | MyS s -> E.mkApp mysc (embed s) []

let mynat_ = API.(AlgebraicData.declare {
  ty = TyName "mynat";
  doc = "blibli";
  pp = (fun fmt _ -> Format.fprintf fmt "<todo>");
  constructors = [
   K("myzero","",N,
     B Myzero,
     M (fun ~ok ~ko -> embed));
   K("mysucc","",S(N),
     B (fun x -> MyS x),
     M (fun ~ok ~ko -> embed))
]
} |> ContextualConversion.(!<))

let builtins =
  API.BuiltIn.declare ~file_name:"ext.elpi" [
    MLData mynat_;
      MLCode(Pred("add1",
    In(mynat_, "mynat",
    Out(mynat_, "mynat",
    Easy("AAA"))),
    fun a _ ~depth -> (), Some (MyS a)),
    DocAbove
  );
]
