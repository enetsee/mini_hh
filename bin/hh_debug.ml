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

(* ~~ Context rendering ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
(*
   let render_local_ctxt local local_rfmts =
  (* We want to render each local variable with the accumulated refinements _and_ the evaluation of those refinements *)
  let init =
    Name.Tm_var.Map.of_alist_exn
    @@ List.map ~f:(fun (tm_var, ty, _spans) -> tm_var, (ty, []))
    @@ Ctxt.Local.bindings local
  in
  let f acc rfmt =
    (* Push each local refinement onto the accumulator for the relavant term var *)
    List.fold_left (Ctxt.Local.Refinement.bindings rfmt) ~init:acc ~f:(fun acc (tm_var, ty_rfmt) ->
      Map.update acc tm_var ~f:(function
        | Some (ty, ty_rfmts) -> ty, ty_rfmt :: ty_rfmts
        | None -> failwith "impossible"))
  in
  let data =
    List.map ~f:(fun (tm_var, (ty, ty_rfmts)) ->
      let refined_ty = List.fold_left ty_rfmts ~init:ty ~f:(fun ty rfmt -> Ty.refine ty ~rfmt) in
      [ Lwd.pure @@ W.string ~attr:Attr.(fg yellow) @@ Name.Tm_var.to_string tm_var
      ; render_ty ty
      ; W.scrollbox @@ W.vlist @@ List.map ty_rfmts ~f:render_ty_refinement
      ; render_ty refined_ty
      ])
    @@ Map.to_alist
    @@ List.fold_left local_rfmts ~init ~f
  in
  let headers =
    List.map
      ~f:Lwd.pure
      [ W.string " Name    |  "; W.string "Type    |  "; W.string "Refinements    |  "; W.string "Refined type" ]
  in
  W.scrollbox @@ W.grid ~h_space:1 ~headers data
;;

let render_ty_param_ctxt (ty_params : Ctxt.Ty_param.t) (ty_param_rfmts : Ctxt.Ty_param.Refinement.t list) =
  let init =
    Name.Ty_param.Map.of_alist_exn
    @@ List.map ~f:(fun (name, bounds) -> name, (bounds, []))
    @@ Ctxt.Ty_param.bindings ty_params
  in
  let f acc rfmt =
    match Ctxt.Ty_param.Refinement.bindings rfmt with
    | `Top -> acc
    | `Bounds bounds ->
      (* Push each local refinement onto the accumulator for the relavant term var *)
      List.fold_left bounds ~init:acc ~f:(fun acc (ty_param_nm, ty_param_bound) ->
        Map.update acc ty_param_nm ~f:(function
          | Some (declared_bounds, ty_param_bounds) -> declared_bounds, ty_param_bound :: ty_param_bounds
          | None -> failwith "impossible"))
    | `Bottom -> failwith "Founds bottom type parameter refinement"
  in
  let data =
    List.map ~f:(fun (ty_param_name, (declard_bounds, bound_rftms)) ->
      let refined_bounds = Ty.Param_bounds.meet_many (declard_bounds :: bound_rftms) ~prov:Prov.empty in
      [ Lwd.pure @@ W.string ~attr:Attr.(fg yellow) @@ Name.Ty_param.to_string ty_param_name
      ; render_ty_param_bounds declard_bounds
      ; W.scrollbox @@ W.vlist @@ List.map bound_rftms ~f:render_ty_param_bounds
      ; render_ty_param_bounds refined_bounds
      ])
    @@ Map.to_alist
    @@ List.fold_left ty_param_rfmts ~init ~f
  in
  let headers =
    List.map
      ~f:Lwd.pure
      [ W.string "Type parameter    |  "
      ; W.string "Declared bounds    |  "
      ; W.string "Refinements    |  "
      ; W.string "Refined bounds"
      ]
  in
  W.scrollbox @@ W.grid ~h_space:1 ~headers data
;;



let render_continuation_context ctxt_cont_opt ctxt_def_opt =
  let cont =
    match ctxt_cont_opt with
    | Some ctxt_cont ->
      [ ( "local context"
        , fun _ ->
            render_local_ctxt ctxt_cont.Ctxt.Cont.bindings.local
            @@ List.filter_map ctxt_cont.Ctxt.Cont.rfmtss ~f:(fun rfmt_opt ->
              Option.map rfmt_opt ~f:(fun rfmt -> rfmt.Ctxt.Cont.Refinements.local)) )
      ; ( "type parameter context"
        , fun _ ->
            render_ty_param_ctxt ctxt_cont.Ctxt.Cont.bindings.ty_param
            @@ List.filter_map ctxt_cont.Ctxt.Cont.rfmtss ~f:(fun rfmt_opt ->
              Option.map rfmt_opt ~f:(fun rfmt -> rfmt.Ctxt.Cont.Refinements.ty_param)) )
      ]
    | _ -> []
  in
  let def =
    Option.value_map ctxt_def_opt ~default:[] ~f:(fun ctxt_def ->
      [ ("definition context", fun _ -> render_def_ctxt ctxt_def) ])
  in
  match cont @ def with
  | [] -> W.empty_lwd
  | uis -> Tabs.view uis
;;

(* ~~ Render expression typing delta ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)

let render_local_refinement_delta local =
  W.scrollbox
  @@ W.vlist
  @@ List.map ~f:(fun (name, ty_rfmt) ->
    W.hbox
      [ Lwd.pure @@ W.string ~attr:Attr.(fg green) @@ Name.Tm_var.to_string name
      ; Lwd.pure @@ Ui.space 1 1
      ; Lwd.pure @@ W.string ~attr:Attr.(fg white) ":"
      ; Lwd.pure @@ Ui.space 3 3
      ; Lwd.pure @@ W.string ~attr:Attr.(fg magenta) @@ Ty.Refinement.show ty_rfmt
      ])
  @@ Ctxt.Local.Refinement.bindings local
;;

let render_ty_param_refinement_delta ty_param =
  match Ctxt.Ty_param.Refinement.bindings ty_param with
  | `Top -> Lwd.pure @@ W.string "(top)"
  | `Bottom -> Lwd.pure @@ W.string "(bottom)"
  | `Bounds bindings ->
    W.scrollbox
    @@ W.vlist
    @@ List.map
         ~f:(fun (name, Ty.Param_bounds.{ lower; upper }) ->
           W.hbox
             [ pad ~right:1 @@ Lwd.pure @@ W.string ~attr:Attr.(fg green ++ st italic) @@ Name.Ty_param.to_string name
             ; pad ~right:2 @@ Lwd.pure @@ W.string ~attr:Attr.(fg white) ":"
             ; pad ~right:1 @@ Lwd.pure @@ W.string ~attr:Attr.(fg white) "{ lower: _ ∨"
             ; render_ty lower
             ; pad ~right:1 @@ Lwd.pure @@ W.string ~attr:Attr.(fg white) ", upper: _ ∧"
             ; render_ty upper
             ; pad ~left:1 @@ Lwd.pure @@ W.string ~attr:Attr.(fg white) "}"
             ])
         bindings
;;

let render_local_delta local =
  W.scrollbox
  @@ W.vlist
  @@ List.map ~f:(fun (tm_var, ty, _spans) ->
    W.hbox [ Lwd.pure @@ W.string ~attr:Attr.(fg yellow) @@ Name.Tm_var.to_string tm_var; render_ty ty ])
  @@ Ctxt.Local.bindings local
;;

let render_ty_param_delta ty_params =
  W.scrollbox
  @@ W.vlist
  @@ List.map ~f:(fun (name, bounds) ->
    W.hbox
      [ pad ~right:2 @@ render_ty bounds.Ty.Param_bounds.lower
      ; pad ~right:2 @@ Lwd.pure @@ W.string ~attr:Attr.(fg white) "<:"
      ; pad ~right:2 @@ Lwd.pure @@ W.string ~attr:Attr.(fg green ++ st italic) @@ Name.Ty_param.to_string name
      ; pad ~right:2 @@ Lwd.pure @@ W.string ~attr:Attr.(fg white) "<:"
      ; render_ty bounds.Ty.Param_bounds.upper
      ])
  @@ Ctxt.Ty_param.bindings ty_params
;;

let render_expr_delta expr_delta =
  Tabs.view
    [ ( "local delta"
      , fun _ ->
          match expr_delta.Ctxt.Cont.Expr_delta.bindings with
          | None -> Lwd.pure @@ W.string "(no change)"
          | Some Ctxt.Cont.Bindings.{ local; _ } -> render_local_delta local )
    ; ( "local refinement delta"
      , fun _ ->
          match expr_delta.Ctxt.Cont.Expr_delta.rfmts with
          | None -> Lwd.pure @@ W.string "(no change)"
          | Some rfmt_delta -> render_local_refinement_delta rfmt_delta.Ctxt.Cont.Refinements.local )
    ; ( "type parameter delta"
      , fun _ ->
          match expr_delta.Ctxt.Cont.Expr_delta.bindings with
          | None -> Lwd.pure @@ W.string "(no change)"
          | Some { ty_param; _ } -> render_ty_param_delta ty_param )
    ; ( "type parameter refinement delta"
      , fun _ ->
          match expr_delta.Ctxt.Cont.Expr_delta.rfmts with
          | None -> Lwd.pure @@ W.string "(no change)"
          | Some rfmt_delta -> render_ty_param_refinement_delta rfmt_delta.Ctxt.Cont.Refinements.ty_param )
    ]
;;

(* ~~ Render per-continuation delta ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)

let render_cont_delta cont_delta =
  Tabs.view
    [ ( "local delta"
      , fun _ ->
          match cont_delta.Ctxt.Cont.Delta.bindings with
          | None -> Lwd.pure @@ W.string "(no change)"
          | Some { local; _ } -> render_local_delta local )
    ; ( "type parameter delta"
      , fun _ ->
          match cont_delta.Ctxt.Cont.Delta.bindings with
          | None -> Lwd.pure @@ W.string "(no change)"
          | Some { ty_param; _ } -> render_ty_param_delta ty_param )
    ]
;;

(* ~~ Render all-continuation delta ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
let render_ctxt_delta ctxt_delta =
  Tabs.view
    [ ( "next continuation"
      , fun _ ->
          match ctxt_delta.Ctxt.Delta.next with
          | None -> Lwd.pure @@ W.string "(empty)"
          | Some delta -> render_cont_delta delta )
    ; ( "exit continuation"
      , fun _ ->
          match ctxt_delta.Ctxt.Delta.exit with
          | None -> Lwd.pure @@ W.string "(empty)"
          | Some delta -> render_cont_delta delta )
    ]
;;

(* ~~ Render refinement requests ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
let render_refinement_request = function
  | Refine_ty { ty_scrut; ty_test } ->
    W.hbox
      [ pad ~right:2 @@ render_ty ty_scrut
      ; pad ~right:2 @@ Lwd.pure @@ W.string ~attr:Attr.(fg white) "<~~"
      ; render_ty ty_test
      ]
  | Refine_existential_scrut { ty_exists; ty_test } ->
    W.hbox
      [ pad ~right:2 @@ render_exists ty_exists
      ; pad ~right:2 @@ Lwd.pure @@ W.string ~attr:Attr.(fg white) "<~~"
      ; render_ty ty_test
      ]
  | Refine_existential_test { ty_scrut; ty_exists } ->
    W.hbox
      [ pad ~right:2 @@ render_ty ty_scrut
      ; pad ~right:2 @@ Lwd.pure @@ W.string ~attr:Attr.(fg white) "<~~"
      ; render_exists ty_exists
      ]
  | Refine_union_scrut { tys_scrut; ty_test } ->
    W.hbox
      [ pad ~right:2 @@ render_union tys_scrut
      ; pad ~right:2 @@ Lwd.pure @@ W.string ~attr:Attr.(fg white) "<~~"
      ; render_ty ty_test
      ]
  | Refine_union_test { ty_scrut; tys_test } ->
    W.hbox
      [ pad ~right:2 @@ render_ty ty_scrut
      ; pad ~right:2 @@ Lwd.pure @@ W.string ~attr:Attr.(fg white) "<~~"
      ; render_union tys_test
      ]
;;

(* ~~ Render details of the current status ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
let render_status_payload payload_opt =
  Option.value_map payload_opt ~default:W.empty_lwd ~f:(function
    | Expr_delta (_span, ty, expr_delta) ->
      W.vbox
        [ W.hbox [ Lwd.pure @@ W.string "Type :"; pad ~left:2 @@ render_ty ty ]
        ; pad ~top:1 @@ Lwd.pure @@ W.string "Refinement:"
        ; pad ~top:1 @@ render_expr_delta expr_delta
        ]
    | Stmt_delta ctxt_delta -> render_ctxt_delta ctxt_delta
    | Rfmt_request rfmt_request -> render_refinement_request rfmt_request
    | Rfmt (ty_rfmt, prov_ty_param_rfmt_opt) ->
      let elems =
        [ W.hbox [ Lwd.pure @@ W.string "Type refinement:"; render_ty_refinement ty_rfmt ]
        ; pad ~top:1 @@ Lwd.pure @@ W.string "Type parameter refinement:"
        ; (match prov_ty_param_rfmt_opt with
           | None -> Lwd.pure @@ W.string "(no type parameter refinement)"
           | Some (_, ty_param) -> render_ty_param_refinement_delta ty_param)
        ]
      in
      W.vbox elems
    | Asked_up { of_; at } ->
      W.hbox
      @@ [ Lwd.pure @@ W.string ~attr:Attr.(fg magenta) @@ Ty.Ctor.show of_
         ; pad ~left:2 ~right:2 @@ Lwd.pure @@ W.string "↑"
         ; Lwd.pure @@ W.string ~attr:Attr.(fg magenta) @@ Name.Ctor.to_string at
         ]
    | Asked_ctor_info ctor_name | Asked_ty_param_variances ctor_name ->
      Lwd.pure @@ W.string ~attr:Attr.(fg yellow) @@ Name.Ctor.to_string ctor_name
    | Raised_error err -> Lwd.pure @@ W.string ~attr:Attr.(fg red) @@ Typing.Err.to_string err
    | Raised_warning warn -> Lwd.pure @@ W.string ~attr:Attr.(fg yellow) @@ Typing.Warn.to_string warn
    | Span span -> Lwd.pure @@ W.string @@ Span.to_string span
    | Empty -> Lwd.pure @@ W.string "(status has no associated data)"
    | Complete -> Lwd.pure @@ W.string ~attr:Attr.(bg green ++ fg white) "complete"
    | Failed exn ->
      Lwd.pure @@ W.string ~attr:Attr.(bg red ++ fg white) @@ Format.sprintf "failed %s" @@ Exn.to_string exn)
;;

(* ~~ Entry point ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)

let def_to_string def =
  match def with
  | Lang.Def.Classish Located.{ elem = Lang.Classish_def.{ kind; name; _ }; _ } ->
    let kind_string = Lang.Classish_kind.to_string @@ Located.elem kind
    and classish_name = Name.Ctor.to_string @@ Located.elem name in
    Format.sprintf "%s %s" kind_string classish_name
  | Lang.Def.Fn Located.{ elem = Lang.Fn_def.{ name; _ }; _ } ->
    let fn_name = Name.Fn.to_string @@ Located.elem name in
    fn_name
;;

let view_def def =
  let on_click _ =
    let _ : unit = Lwd.set st_current_def (Some def) in
    let comp _ = Typing.Def.synth def in
    let step = Typing.Eff.Debug.go comp in
    let _ : unit = Lwd.set st_step (Some step) in
    let _ : unit = update_step step in
    ()
  in
  let label = def_to_string def in
  W.button ~attr:Notty.A.(st underline ++ fg blue) label on_click
;; *)

(* let start file =
  let open Nottui in
  let update_file file =
    let _ : unit = Lwd.set st_file (Some file) in
    let _ : unit = Lwd.set st_span None in
    let _ : unit = Lwd.set st_current_def None in
    let _ : unit = Lwd.set st_step None in
    ()
  in
  let w =
    W.h_pane
      ((* Left-most pane contains file explorer (top) and list of top-level definitions for the file (bottom) *)
       W.v_pane
         (W.vbox
            [ pad ~left:1 ~bottom:1 @@ Lwd.pure @@ W.string ~attr:Attr.(fg cyan ++ st underline) @@ "Files"
            ; File_select.view file ~on_select:update_file ()
            ])
         (W.vbox
            [ pad ~left:1 ~bottom:1 @@ Lwd.pure @@ W.string ~attr:Attr.(fg cyan ++ st underline) @@ "Definitions"
            ; Lwd.pure @@ Ui.space 0 1
            ; W.scrollbox @@ W.vlist_with (fun def -> Lwd.pure @@ view_def def) st_defs
            ]))
      (W.v_pane
         (W.h_pane
            (* ~~ The currently loaded file, definition and span ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
            (W.vbox
               [ pad ~left:1 ~bottom:1
                 @@ W.hbox
                      [ Lwd.map (Lwd.get st_file) ~f:(fun file_opt ->
                          let attr =
                            if Option.is_none file_opt then Attr.(fg @@ gray 10) else Attr.(bg white ++ fg black)
                          in
                          W.string ~attr
                          @@ Option.value_map ~f:(fun s -> s ^ "  /") ~default:"no file selected  /" file_opt)
                      ; Lwd.map (Lwd.get st_current_def) ~f:(fun def_opt ->
                          let attr =
                            if Option.is_none def_opt then Attr.(fg @@ gray 10) else Attr.(bg white ++ fg black)
                          in
                          W.string ~attr
                          @@ Option.value_map
                               ~default:"  no definition selected  /"
                               ~f:(fun def -> def_to_string def ^ "  /")
                               def_opt)
                      ; Lwd.map (Lwd.get st_step) ~f:(fun step_opt ->
                          let attr =
                            if Option.is_none step_opt then Attr.(fg @@ gray 10) else Attr.(bg white ++ fg black)
                          in
                          let span_opt = Option.map step_opt ~f:Typing.Eff.Debug.Step.current_span in
                          W.string ~attr
                          @@ Option.value_map
                               ~default:"  not debugging"
                               ~f:(fun span -> "  " ^ Span.to_string span)
                               span_opt)
                      ]
                 (* ~~ The currently loaded file ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
               ; W.scrollbox
                 @@ Lwd.join
                 @@ Lwd.map2 st_source (Lwd.get st_span) ~f:(fun lines span_opt -> render_program lines span_opt)
               ])
            (Lwd.bind (Lwd.map ~f:(Option.map ~f:Typing.Eff.Debug.Step.state) @@ Lwd.get st_step) ~f:render_state))
         (W.hbox
            [ W.h_pane
                (Lwd.join @@ Lwd.map2 (Lwd.get st_ctxt_cont) (Lwd.get st_ctxt_def) ~f:render_continuation_context)
                (W.vbox
                   [ pad ~left:1 ~bottom:1 nav
                   ; pad ~left:1
                     @@ Lwd.map (Lwd.get st_status_name) ~f:(fun status_opt ->
                       match status_opt with
                       | None -> W.string ~attr:Attr.(fg @@ gray 10) "(not debugging)"
                       | Some txt -> W.string ~attr:Attr.(st bold ++ fg magenta) txt)
                   ; pad ~left:1 ~top:1 @@ Lwd.bind (Lwd.get st_status_payload) ~f:render_status_payload
                   ])
            ]))
  in
  Ui_loop.run w
;; *)

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
      [ Lwd.pure @@ Button.view ~label:"< step back" ~on_click:prev ~enabled
      ; Lwd.pure @@ Button.view ~label:"step forward >" ~on_click:next ~enabled
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
