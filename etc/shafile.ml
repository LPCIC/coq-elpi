let () =
  Sys.argv |> Array.iter (fun file ->
    Printf.printf "%s: %s\n" file @@ Digest.to_hex @@ Digest.file file)