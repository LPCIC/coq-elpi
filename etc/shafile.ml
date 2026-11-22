let mk_ident =
  String.map (function 'a'..'z' | 'A'..'Z' | '0'..'9' | '_' as c -> c | _ -> '_')

let () =
  Printf.printf "Local Set Warnings \"-abstract-large-number\".\n";
  (* argv.(0) is this program (maybe /path/4.14.2+flambda/bin/...) *)
  Sys.argv |> Array.iteri (fun i file -> if i > 0 then
    Printf.printf "Definition %s := 0x%s.\n"
      (mk_ident file) @@ Digest.to_hex @@ Digest.file file)
