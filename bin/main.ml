open Why3

let usage = "icon <file>"

(* let () = *)
(*   Arg.parse [] *)
(*     (fun file -> *)
(*       Format.printf "%a@." (Mlw_printer.pp_mlw_file ~attr:true) *)
(*       @@ Gen_mlw.file @@ Translator.parse_file file) *)
(*     usage *)

let () =
  Arg.parse []
    (fun file ->
      In_channel.with_open_text file (fun ic ->
          let lexbuf = Lexing.from_channel ic in
          Lexing.set_filename lexbuf file;
          let f = Lexer.parse_mlw_file lexbuf in
          Format.printf "%a@." (Mlw_printer.pp_mlw_file ~attr:true)
          @@ Gen_mlw.from_mlw f))
    usage

(* let mlw_file = Gen_mlw.file @@ Translator.parse_file "test/dexter_c.mlw" *)
(* let () = Format.printf "%a@." (Mlw_printer.pp_mlw_file ~attr:true) mlw_file *)
(* let config : Whyconf.config = Whyconf.init_config None *)
(* let main : Whyconf.main = Whyconf.get_main config *)
(* let libdir = Whyconf.libdir main *)
(* let datadir = Whyconf.datadir main *)
(* let env : Env.env = Env.create_env ("./whyml/stdlib" :: Whyconf.loadpath main) *)
(* let mods = Typing.type_mlw_file env [] "myfile.mlw" mlw_file *)
