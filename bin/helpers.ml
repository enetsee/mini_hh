open Nottui
module W = Nottui_widgets

let pad ?(top = 0) ?(left = 0) ?(bottom = 0) ?(right = 0) ui =
  W.hbox
    [ Lwd.pure @@ Ui.space left 0
    ; W.vbox [ Lwd.pure @@ Ui.space 0 top; ui; Lwd.pure @@ Ui.space 0 bottom ]
    ; Lwd.pure @@ Ui.space right 0
    ]
;;
