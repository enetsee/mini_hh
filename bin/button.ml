open Core
open Nottui
module W = Nottui_widgets
module Attr = Notty.A

let view ~label ~on_click ~enabled =
  let ln = String.length label + 2 in
  let hline = String.concat @@ List.init ln ~f:(fun _ -> "═") in
  let top = "╔" ^ hline ^ "╗" in
  let bottom = "╚" ^ hline ^ "╝" in
  let left, right = "║ ", " ║" in
  let attr_surround =
    if enabled
    then Attr.(st bold ++ fg white)
    else Attr.(st bold ++ fg (gray 4))
  and attr_label =
    if enabled then Attr.(st underline ++ fg blue) else Attr.(fg (gray 10))
  in
  let ui_top = Ui.atom @@ Notty.I.string attr_surround top
  and ui_bottom = Ui.atom @@ Notty.I.string attr_surround bottom
  and ui_left = Ui.atom @@ Notty.I.string attr_surround left
  and ui_right = Ui.atom @@ Notty.I.string attr_surround right
  and ui_label = Ui.atom @@ Notty.I.string attr_label label
  and handler =
    if enabled
    then (fun ~x:_ ~y:_ _ ->
      on_click ();
      `Handled)
    else fun ~x:_ ~y:_ _ -> `Handled
  in
  Ui.mouse_area
    handler
    (Ui.vcat [ ui_top; Ui.hcat [ ui_left; ui_label; ui_right ]; ui_bottom ])
;;

let view_string ?(attr = Attr.empty) label ~on_click ~enabled ~breakpoint =
  let handler =
    if enabled
    then (fun ~x:_ ~y:_ _ ->
      on_click ();
      `Handled)
    else fun ~x:_ ~y:_ _ -> `Handled
  and ui_break =
    Ui.atom
    @@
    if breakpoint
    then Notty.I.string Attr.(attr ++ fg red) "■"
    else Notty.I.string attr " "
  and ui_label = Ui.atom @@ Notty.I.string attr label in
  Ui.mouse_area handler (Ui.hcat [ ui_break; ui_label ])
;;
