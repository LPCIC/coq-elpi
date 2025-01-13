
let main () =
  let v = Sys.argv.(1) in
  let a,b,c = Elpi.API.Utils.version_parser ~what:"elpi" v in
  let open Format in
  printf "(%d,%d,%d)%!" a b c
;;

main ()
