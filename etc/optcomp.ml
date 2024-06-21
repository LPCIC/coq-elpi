let () =
  let v = Sys.argv.(1) in
  let ic = open_in Sys.argv.(2) in
  let only = Str.regexp "^#\\[only=\"\\([^\"]+\\)\"\\] *" in
  let skip = Str.regexp "^#\\[skip=\"\\([^\"]+\\)\"\\] *" in
  let has rex l =
    if Str.string_match rex l 0 then
      let expr = Str.matched_group 1 l in
      Some (Str.regexp expr, Str.replace_first rex "" l)
    else None in
  try
    while true do
      let l = input_line ic in
      begin match has only l, has skip l with
      | None, None -> print_string l
      | Some (r,l), None when Str.string_match r v 0 -> print_string l
      | Some _, None -> ()
      | None, Some (r,_) when Str.string_match r v 0 -> ()
      | None, Some (_,l) -> print_string l
      | Some _, Some _ -> assert false
      end; print_newline ()
    done
  with End_of_file -> exit 0