open Core
open Nottui
module W = Nottui_widgets
module Attr = Notty.A

let view path ?filter ~(on_select : string -> unit) () : Ui.t Lwd.t =
  let rec aux ~fold path =
    try
      let p_rel = if String.equal path "" then "." else path in
      match Sys_unix.is_directory p_rel with
      | `Yes ->
        let ui () =
          let arr = Sys_unix.readdir p_rel in
          let l = Array.to_list arr |> List.map ~f:(Filename.concat path) in
          (* apply potential filter *)
          let l =
            match filter with
            | None -> l
            | Some f -> List.filter ~f l
          in
          let l = Lwd.return @@ List.sort ~compare:String.compare l in
          W.vlist_with ~bullet:"" (aux ~fold:true) l
        in
        if fold
        then
          W.unfoldable
            ~folded_by_default:true
            (Lwd.return @@ W.string @@ path ^ "/")
            ui
        else ui ()
      | _ ->
        let basename = Filename.basename path in
        Lwd.return
        @@ W.button
             ~attr:Notty.A.(st underline ++ fg blue)
             basename
             (fun () -> on_select path)
    with
    | e ->
      Lwd.return
      @@ Ui.vcat
           [ W.printf ~attr:Notty.A.(bg red) "cannot list directory %s" path
           ; W.string @@ Exn.to_string e
           ]
  in
  aux ~fold:false path
;;
