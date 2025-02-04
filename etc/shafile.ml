let mk_ident =
  String.map (function '.' | '/' | '-' -> '_' | c -> c)

let () =
  Sys.argv |> Array.iter (fun file ->
    Printf.printf "Definition %s := 0x%s.\n"
      (mk_ident file) @@ Digest.to_hex @@ Digest.file file)
