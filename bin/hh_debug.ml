let init _ = Minttea.Command.Seq [ Enter_alt_screen ]

type model =
  { file : string
  ; source : string
  (* ; oracle : Oracle.t
     ; ast : Lang.Def.t list *)
  }

let update event (model : model) =
  let open Minttea in
  match event with
  | _ -> model, Command.Noop
;;

let view model = model.source

(* ~~ Entry point ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)

let start file =
  let ch_in = In_channel.open_text file in
  let source = In_channel.input_all ch_in in
  (* let ast = Source.Parse.parse_string_exn source in
     let oracle = Oracle.empty in *)
  let initial_model = { file; source } in
  (* ; ast; oracle } in *)
  Minttea.start ~initial_model @@ Minttea.app ~init ~update ~view ()
;;

let cmd =
  let open Cmdliner in
  let file = Arg.(value & pos 0 non_dir_file "" & info []) in
  let info = Cmd.info "hh_debug" in
  let term = Term.(const start $ file) in
  Cmd.v info term
;;

let main () = exit Cmdliner.(Cmd.eval cmd)
let () = main ()

(* let command =
  Command.basic
    ~summary:"Interactive type checking debugger for mini-hh"
    (let%map_open.Command file = anon ("filename" %: Filename_unix.arg_type) in
     fun () ->
       let ch_in = In_channel.open_text file in
       let source = In_channel.input_all ch_in in
       let ast = Source.Parse.parse_string_exn source in
       let oracle = Oracle.empty in
       let initial_model = { file; source; ast; oracle } in
       Minttea.start ~initial_model @@ Minttea.app ~init ~update ~view ()) *)

(* let () = Command_unix.run ~version:"1.0" ~build_info:"RWO" command *)
