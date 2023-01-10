open Why3

let () =
  Format.printf "%a@." (Mlw_printer.pp_mlw_file ~attr:true) (Gen_mlw.file ())
