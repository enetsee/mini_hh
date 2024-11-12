open Core
open Reporting
open Nottui
module W = Nottui_widgets
module Attr = Notty.A

let logo =
  [ "                                                                          "
  ; "    ██╗  ██╗██╗  ██╗        ██████╗ ███████╗██████╗ ██╗   ██╗ ██████╗     "
  ; "    ██║  ██║██║  ██║        ██╔══██╗██╔════╝██╔══██╗██║   ██║██╔════╝     "
  ; "    ███████║███████║        ██║  ██║█████╗  ██████╔╝██║   ██║██║  ███╗    "
  ; "    ██╔══██║██╔══██║        ██║  ██║██╔══╝  ██╔══██╗██║   ██║██║   ██║    "
  ; "    ██║  ██║██║  ██║███████╗██████╔╝███████╗██████╔╝╚██████╔╝╚██████╔╝    "
  ; "    ╚═╝  ╚═╝╚═╝  ╚═╝╚══════╝╚═════╝ ╚══════╝╚═════╝  ╚═════╝  ╚═════╝     "
  ]
;;

let model : Debugging.Model.t Lwd.var = Lwd.var Debugging.Model.Uninit

let update action =
  Lwd.set model @@ Debugging.Model.update (Lwd.peek model) ~action
;;

let next () = update Debugging.Model.Action.Next
let prev () = update Debugging.Model.Action.Prev
let select_file file = update @@ Debugging.Model.Action.Select_file file
let select_def def = update @@ Debugging.Model.Action.Select_def def

let toggle_breakpoint line =
  update @@ Debugging.Model.Action.(Toggle_breakpoint line)
;;

let run () = update @@ Debugging.Model.Action.Run
let restart () = update @@ Debugging.Model.Action.Restart

module Definitions = struct
  let def_to_string def =
    match def with
    | Lang.Def.Classish
        Located.{ elem = Lang.Classish_def.{ kind; name; _ }; _ } ->
      let kind_string = Lang.Classish_kind.to_string @@ Located.elem kind
      and classish_name = Name.Ctor.to_string @@ Located.elem name in
      Format.sprintf "%s %s" kind_string classish_name
    | Lang.Def.Fn Located.{ elem = Lang.Fn_def.{ name; _ }; _ } ->
      let fn_name = Name.Fn.to_string @@ Located.elem name in
      fn_name
  ;;

  let view_def def =
    let label = def_to_string def in
    let on_click _ = select_def def in
    Lwd.pure @@ W.button ~attr:Attr.(st underline ++ fg blue) label on_click
  ;;

  let render defs = W.scrollbox @@ W.vlist @@ List.map ~f:view_def defs
end

let nav =
  Lwd.bind (Lwd.get model) ~f:(fun model ->
    let enabled = Debugging.Model.is_debugging model in
    W.hbox
      [ Lwd.pure @@ Button.view ~label:"<< restart" ~on_click:restart ~enabled
      ; Lwd.pure @@ Button.view ~label:"< step back" ~on_click:prev ~enabled
      ; Lwd.pure @@ Button.view ~label:"step forward >" ~on_click:next ~enabled
      ; Lwd.pure @@ Button.view ~label:"run >>" ~on_click:run ~enabled
      ])
;;

let h1 title =
  Helpers.pad ~bottom:1 ~left:1
  @@ Lwd.pure
  @@ W.string ~attr:Attr.(st bold ++ fg cyan) title
;;

let h2 title =
  Helpers.pad ~left:1
  @@ Lwd.pure
  @@ W.string ~attr:Attr.(st bold ++ fg magenta) title
;;

let start start_directory =
  let _ : unit = Lwd.set model @@ Debugging.Model.Init { start_directory } in
  let file_and_def_select =
    W.v_pane
      (W.vbox
         [ h1 "Files"
         ; W.scrollbox
           @@ File_select.view start_directory ~on_select:select_file ()
         ])
      (W.vbox
         [ h1 "Definitions"
         ; Lwd.bind (Lwd.get model) ~f:(fun model ->
             Definitions.render @@ Debugging.Model.definitions model)
         ])
  in
  let program =
    W.vbox
      [ Lwd.bind (Lwd.get model) ~f:(fun model ->
          let lines =
            Option.value ~default:logo @@ Debugging.Model.source_opt model
          and span_opt = Debugging.Model.span_opt model
          and breakpoints = Debugging.Model.breakpoints model in
          W.scrollbox
          @@ View.Program_view.render
               lines
               span_opt
               ~breakpoints
               ~on_click:toggle_breakpoint)
      ; nav
      ]
  in
  let status =
    Lwd.bind (Lwd.get model) ~f:(fun model ->
      W.vbox
        [ h2 "Status"
        ; Option.value_map ~default:W.empty_lwd ~f:(fun ctxt_def ->
            W.scroll_area @@ View.Status.render ctxt_def)
          @@ Debugging.Model.status_opt model
        ])
  in
  let top = W.h_pane (W.h_pane file_and_def_select program) status in
  let state =
    Lwd.bind (Lwd.get model) ~f:(fun model ->
      W.vbox
        [ h2 "State"; View.State_view.render @@ Debugging.Model.state model ])
  in
  let ctxt_def =
    Lwd.bind (Lwd.get model) ~f:(fun model ->
      W.vbox
        [ h2 "Defintion context"
        ; Option.value_map ~default:W.empty_lwd ~f:(fun ctxt_def ->
            W.scroll_area @@ View.Ctxt_def.render ctxt_def)
          @@ Debugging.Model.ctxt_def_opt model
        ])
  in
  let ctxt_cont =
    Lwd.bind (Lwd.get model) ~f:(fun model ->
      let ctxt_def = Debugging.Model.ctxt_cont_opt model in
      W.vbox
        [ h2 "Continuation context"
        ; Helpers.pad ~top:1 ~left:1
          @@ W.scroll_area
          @@ View.Ctxt_cont.render ctxt_def
        ])
  in
  let bottom = W.h_pane (W.v_pane state ctxt_def) ctxt_cont in
  let w = W.v_pane top bottom in
  Ui_loop.run w
;;

let cmd =
  let open Cmdliner in
  let file = Arg.(value & pos 0 dir "" & info []) in
  let info = Cmd.info "hh_debug" in
  let term = Term.(const start $ file) in
  Cmd.v info term
;;

let main () = exit Cmdliner.(Cmd.eval cmd)
let () = main ()
