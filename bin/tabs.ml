open Core
open Helpers
open Lwd.Infix
open Nottui
module Attr = Notty.A

let render_tab_active label =
  let ln = String.length label + 2 in
  let hline = String.concat @@ List.init ln ~f:(fun _ -> "═") in
  let hspace = String.concat @@ List.init ln ~f:(fun _ -> " ") in
  let top = " ╔" ^ hline ^ "╗ " in
  let bottom = "═╝" ^ hspace ^ "╚═" in
  let left, right = " ║ ", " ║ " in
  let attr_surround = Attr.(st bold ++ fg white)
  and attr_label = Attr.(st underline ++ fg blue) in
  let ui_top = Ui.atom @@ Notty.I.string attr_surround top
  and ui_bottom = Ui.atom @@ Notty.I.string attr_surround bottom
  and ui_left = Ui.atom @@ Notty.I.string attr_surround left
  and ui_right = Ui.atom @@ Notty.I.string attr_surround right
  and ui_label = Ui.atom @@ Notty.I.string attr_label label in
  Ui.vcat [ ui_top; Ui.hcat [ ui_left; ui_label; ui_right ]; ui_bottom ]
;;

let render_tab label =
  let ln = String.length label + 2 in
  let hline = String.concat @@ List.init ln ~f:(fun _ -> "─") in
  let hspace = String.concat @@ List.init ln ~f:(fun _ -> " ") in
  let top = " ┌" ^ hline ^ "┐ " in
  let bottom = "─┘" ^ hspace ^ "└─" in
  let left, right = " │ ", " │ " in
  let attr_surround = Attr.(fg @@ gray 10)
  and attr_label = Attr.(fg lightblue) in
  let ui_top = Ui.atom @@ Notty.I.string attr_surround top
  and ui_bottom = Ui.atom @@ Notty.I.string attr_surround bottom
  and ui_left = Ui.atom @@ Notty.I.string attr_surround left
  and ui_right = Ui.atom @@ Notty.I.string attr_surround right
  and ui_label = Ui.atom @@ Notty.I.string attr_label label in
  Ui.vcat [ ui_top; Ui.hcat [ ui_left; ui_label; ui_right ]; ui_bottom ]
;;

let view () tabs =
  let cur = Lwd.var 0 in
  match tabs with
  | [] -> Lwd.return Ui.empty
  | _ ->
    Lwd.bind (Lwd.get cur) ~f:(fun idx_sel ->
      let _, f = List.nth_exn tabs idx_sel in
      let tab_bar =
        tabs
        |> List.mapi ~f:(fun i (s, _) ->
          let tab_annot =
            if i = idx_sel then render_tab_active s else render_tab s
          in
          Ui.mouse_area
            (fun ~x:_ ~y:_ l ->
              match l with
              | `Left ->
                Lwd.set cur i;
                `Handled
              | _ -> `Unhandled)
            tab_annot)
        |> Ui.hcat
      in
      pad ~left:1 ~right:1 ~top:1 @@ f () >|= Ui.join_y tab_bar)
;;
