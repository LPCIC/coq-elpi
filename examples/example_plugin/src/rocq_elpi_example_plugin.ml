open Elpi.API
let c = AlgebraicData.(declare {
  ty = Conversion.TyName "stuff";
  doc = "doc";
  pp = (fun fmt (x : int) -> ());
  constructors = [
    K("stuff","",A(BuiltInData.int,N),B (fun x -> x),M (fun ~ok ~ko:_ x -> ok x));
  ];
}
) |> ContextualConversion.(!<)

let builtins =
  let open BuiltIn in
  let open BuiltInPredicate in
  let cx = MLData c in
  let q = MLCode(Pred("q",In(c,"xxx",Easy "bla"),(fun i ~depth -> Printf.eprintf "ok %d\n%!" i)),DocAbove) in
  declare ~file_name:"elpi_example_plugin.elpi" [ cx; q ]