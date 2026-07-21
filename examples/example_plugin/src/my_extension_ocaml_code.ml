module API = Elpi.API
module E = API.RawData

(* An algrbraic data type in OCaml, with an API we want to expose *)
type myType = Constant : int -> myType | SumOf : (myType * myType) -> myType
let rec compute (s : myType) = match s with
  | Constant n -> n
  | SumOf (s1, s2) -> compute s1 + compute s2

(* declaring the elpi symbol corresponding to the constructors of myType *)
let constant = E.Constants.declare_global_symbol "constant"
let sumof = E.Constants.declare_global_symbol "sumof"

(* declaring the embed/readback function linking OCaml and Elpi *)
let myType : myType API.Conversion.t = API.(AlgebraicData.declare {
  ty = TyName "myType";
  doc = "description for the new elpi type";
  pp = (fun fmt _ -> Format.fprintf fmt "<todo>");
  constructors = [
   K("constant","",A(BuiltInData.int, N),
     B (fun x -> Constant x),
     M (fun ~ok ~ko  t -> match t with Constant n -> ok n | _ -> ko ()));
   K("sumof","",S(S(N)),
     B (fun x y -> SumOf (x, y)),
     M (fun ~ok ~ko t -> match t with SumOf (x,y) -> ok x y | _ -> ko ()))
]
} |> ContextualConversion.(!<))

(* declaring a new API *)
let compute_api =
  API.BuiltIn.MLCode(Pred("compute",
    In(myType, "Expression",
    Out(myType, "Result",
    Easy("Result is the normal form of Expression"))),
    (* The implementation of the API is the result of compute *)
      (fun a _ ~depth:_ -> (), Some (Constant (compute a)))),
    DocAbove)

(* we declare the neame of the file in which the new API are declared
   and what are the new elpi object defined *)
let builtins = API.BuiltIn.declare ~file_name:"myExtension.elpi" [
  MLData myType;
  compute_api
]

(* The gen_doc tool will generate the Elpi code




*)
