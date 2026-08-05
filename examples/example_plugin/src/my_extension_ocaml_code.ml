module API = Elpi.API
module E = API.RawData

(* An algerbraic data type with the API we want to expose: myType and compute *)
type myType = Constant : int -> myType | SumOf : (myType * myType) -> myType
let rec compute (s : myType) = match s with
  | Constant n -> n
  | SumOf (s1, s2) -> compute s1 + compute s2

(* Declaring the elpi symbol corresponding to the constructors of myType
   is optional, only needed if one users the RawData APIs *)
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

(* we declare the name of the file in which the new builtins are declared
   and the exported stuff (data types and predicates) *)
let builtins = API.BuiltIn.declare ~file_name:"myExtension.elpi" [
  MLData myType;
  compute_api
]

