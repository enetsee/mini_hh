open Core
open Helpers
open Reporting
open Nottui
module W = Nottui_widgets
module Attr = Notty.A

module Ty_view = struct
  let render_base base =
    Lwd.pure @@ W.string ~attr:Attr.(fg blue) @@ Common.Base.to_string base
  ;;

  let rec render t =
    let open Ty.Node in
    match t.Ty.node with
    | Base base -> render_base base
    | Nonnull -> Lwd.pure @@ W.string ~attr:Attr.(fg cyan) "nonnull"
    | Generic name ->
      Lwd.pure
      @@ W.string ~attr:Attr.(fg green ++ st italic)
      @@ Name.Ty_param.to_string name
    | Tuple tuple -> render_tuple tuple
    | Fn fn -> render_fn fn
    | Ctor ctor -> render_ctor ctor
    | Exists exists -> render_exists exists
    | Union [] -> Lwd.pure @@ W.string ~attr:Attr.(fg cyan) "nothing"
    | Union tys -> render_union tys
    | Inter [] -> Lwd.pure @@ W.string ~attr:Attr.(fg cyan) "mixed"
    | Inter tys -> render_intersection tys

  and render_union tys =
    W.hbox
      [ Lwd.pure @@ W.string "("
      ; W.hbox
        @@ List.intersperse
             ~sep:(pad ~left:1 ~right:1 @@ Lwd.pure @@ W.string "|")
        @@ List.map tys ~f:render
      ; Lwd.pure @@ W.string ")"
      ]

  and render_intersection tys =
    W.hbox
      [ Lwd.pure @@ W.string "("
      ; W.hbox
        @@ List.intersperse
             ~sep:(pad ~left:1 ~right:1 @@ Lwd.pure @@ W.string "&")
        @@ List.map tys ~f:render
      ; Lwd.pure @@ W.string ")"
      ]

  and render_tuple Ty.Tuple.{ required; optional; variadic } =
    let sep = pad ~left:1 ~right:1 @@ Lwd.pure @@ W.string "," in
    let req = W.hbox @@ List.intersperse ~sep @@ List.map required ~f:render
    and optional =
      match optional with
      | [] -> W.empty_lwd
      | _ ->
        W.hbox
        @@ (sep
            :: (List.intersperse ~sep
                @@ List.map optional ~f:(fun ty ->
                  W.hbox
                    [ pad ~right:1 @@ Lwd.pure @@ W.string "optional"
                    ; render ty
                    ])))
    and variadic =
      Option.value_map variadic ~default:W.empty_lwd ~f:(fun ty ->
        W.hbox [ sep; render ty; Lwd.pure @@ W.string "..." ])
    in
    let elems = W.hbox [ req; optional; variadic ] in
    W.hbox
      [ pad ~right:1 @@ Lwd.pure @@ W.string "("
      ; elems
      ; pad ~left:1 @@ Lwd.pure @@ W.string ")"
      ]

  and render_fn Ty.Fn.{ params; return } =
    W.hbox
      [ Lwd.pure @@ W.string "("
      ; render_tuple params
      ; pad ~right:1 @@ Lwd.pure @@ W.string ":"
      ; render return
      ; Lwd.pure @@ W.string ")"
      ]

  and render_ctor Ty.Ctor.{ name; args } =
    match args with
    | [] ->
      Lwd.pure @@ W.string ~attr:Attr.(fg lightcyan) @@ Name.Ctor.to_string name
    | _ ->
      W.hbox
        [ Lwd.pure
          @@ W.string ~attr:Attr.(fg lightcyan)
          @@ Name.Ctor.to_string name
        ; Lwd.pure @@ W.string "<"
        ; W.hbox
          @@ List.intersperse ~sep:(pad ~right:1 @@ Lwd.pure @@ W.string ",")
          @@ List.map args ~f:render
        ; Lwd.pure @@ W.string ">"
        ]

  and render_exists Ty.Exists.{ quants; body } =
    W.hbox
      [ pad ~right:1 @@ Lwd.pure @@ W.string ~attr:Attr.(st bold) "∃"
      ; W.hbox
        @@ List.intersperse ~sep:(pad ~right:1 @@ Lwd.pure @@ W.string ",")
        @@ List.map quants ~f:render_quant
      ; pad ~right:1 @@ Lwd.pure @@ W.string ~attr:Attr.(st bold) "."
      ; render body
      ]

  and render_quant quant =
    W.hbox
      [ Lwd.pure @@ W.string "("; render_param quant; Lwd.pure @@ W.string ")" ]

  and render_param Ty.Param.{ name; param_bounds } =
    W.hbox
      [ pad ~right:1
        @@ Lwd.pure
        @@ W.string ~attr:Attr.(fg green ++ st italic)
        @@ Name.Ty_param.to_string name.elem
      ; render_param_bounds param_bounds
      ]

  and render_param_bounds Ty.Param_bounds.{ upper; lower } =
    W.hbox
      [ pad ~right:1 @@ Lwd.pure @@ W.string ~attr:Attr.(st italic) "as"
      ; pad ~right:1 @@ render upper
      ; pad ~right:1 @@ Lwd.pure @@ W.string ~attr:Attr.(st italic) "super"
      ; render lower
      ]
  ;;

  let render_refinement ty_rfmt =
    match ty_rfmt with
    | Ty.Refinement.Disjoint _ ->
      W.hbox
        [ pad ~right:1 @@ Lwd.pure @@ W.string "_"
        ; Lwd.pure @@ W.string "←"
        ; pad ~left:1 @@ Lwd.pure @@ W.string "⊥"
        ]
    | Ty.Refinement.Intersect_with (_, ty) ->
      W.hbox
        [ pad ~right:1 @@ Lwd.pure @@ W.string "_"
        ; Lwd.pure @@ W.string "&"
        ; pad ~left:1 @@ render ty
        ]
    | Ty.Refinement.Replace_with ty ->
      W.hbox
        [ pad ~right:1 @@ Lwd.pure @@ W.string "_"
        ; Lwd.pure @@ W.string "←"
        ; pad ~left:1 @@ render ty
        ]
  ;;
end

module Program_view = struct
  let cursor_l = "»"
  let cursor_r = "«"

  (* ~~ State ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
  let render_line
    gutter_width
    pred
    start_col
    end_col
    breakpoints
    on_click
    line_idx
    line
    =
    let line_num = line_idx + 1 in
    let is_contained, is_start, is_end = pred line_num in
    let line_ui =
      List.map ~f:Lwd.pure
      @@
      if is_contained
      then
        if is_start && is_end
        then
          [ W.string ~attr:Attr.(fg lightwhite) (String.prefix line start_col)
          ; W.string ~attr:Attr.(fg magenta) cursor_l
          ; W.string ~attr:Attr.(fg green) (String.slice line start_col end_col)
          ; W.string ~attr:Attr.(fg magenta) cursor_r
          ; W.string
              ~attr:Attr.(fg lightwhite)
              (String.drop_prefix line end_col)
          ]
        else if is_start
        then
          [ W.string ~attr:Attr.(fg lightwhite) (String.prefix line start_col)
          ; W.string ~attr:Attr.(fg magenta) cursor_l
          ; W.string ~attr:Attr.(fg green) (String.drop_prefix line start_col)
          ]
        else if is_end
        then
          [ W.string ~attr:Attr.(fg green) (String.prefix line end_col)
          ; W.string ~attr:Attr.(fg magenta) cursor_r
          ; W.string
              ~attr:Attr.(fg lightwhite)
              (String.drop_prefix line end_col)
          ]
        else [ W.string ~attr:Attr.(fg green) line ]
      else [ W.string ~attr:Attr.(fg @@ gray 10) line ]
    in
    let space_ui = Lwd.pure (Ui.space 2 0) in
    let gutter_ui =
      Lwd.pure
      @@ Button.view_string
           ~attr:Attr.(st italic ++ fg black ++ bg lightyellow)
           ((String.pad_right ~len:gutter_width @@ Int.to_string line_num)
            ^ " │")
           ~on_click:(fun _ -> on_click line_num)
           ~breakpoint:(Set.mem breakpoints line_num)
           ~enabled:true
    in
    W.hbox (gutter_ui :: space_ui :: line_ui)
  ;;

  let render lines span_opt ~breakpoints ~on_click =
    let gutter_width = String.length @@ Int.to_string @@ List.length lines in
    let pred =
      match span_opt with
      | None -> fun _ -> false, false, false
      | Some Span.{ start_; end_ } ->
        fun line_num ->
          ( line_num >= start_.line && line_num <= end_.line
          , line_num = start_.line
          , line_num = end_.line )
    in
    let start_col, end_col =
      Option.value_map span_opt ~default:(0, 1) ~f:(fun Span.{ start_; end_ } ->
        let start_ = start_.offset - start_.bol
        and end_ = end_.offset - end_.bol in
        start_, end_)
    in
    W.vbox
      (List.mapi
         lines
         ~f:
           (render_line
              gutter_width
              pred
              start_col
              end_col
              breakpoints
              on_click))
  ;;
end

module State_view = struct
  let render_errors errs =
    W.vlist
    @@ List.map errs ~f:(fun err ->
      Lwd.pure @@ W.string @@ Typing.Err.to_string err)
  ;;

  let render_warnings warns =
    W.vlist
    @@ List.map warns ~f:(fun warn ->
      Lwd.pure @@ W.string @@ Typing.Warn.to_string warn)
  ;;

  let render_types span_tys =
    W.vlist
    @@ List.map span_tys ~f:(fun (span, ty) ->
      W.hbox
        [ Lwd.pure @@ W.string ~attr:Attr.(fg @@ gray 10) @@ Span.to_string span
        ; Lwd.pure @@ Ui.space 1 0
        ; Lwd.pure @@ Ui.space 1 0
        ; Ty_view.render ty
        ])
  ;;

  let render state_opt =
    match state_opt with
    | Some Debugging.State.{ tys; errs; warns; _ } ->
      Tabs.view
        [ ("types", fun _ -> render_types tys)
        ; ("errors", fun _ -> render_errors errs)
        ; ("warnings", fun _ -> render_warnings warns)
        ]
    | _ -> W.empty_lwd
  ;;
end

module Ctxt_def = struct
  let render_classish_ctxt ctxt =
    Lwd.pure @@ W.string @@ Ctxt.Classish_def.show ctxt
  ;;

  let render_fn_ctxt ctxt = Lwd.pure @@ W.string @@ Ctxt.Fn_def.show ctxt

  let render (ctxt_def : Ctxt.Def.t) =
    let Ctxt.Def.{ classish; fns } = ctxt_def in
    match classish, fns with
    | None, [] -> W.empty_lwd
    | None, fn_ctxt :: _ -> render_fn_ctxt fn_ctxt
    | Some classish, [] -> render_classish_ctxt classish
    | Some classish, fn_ctxt :: _ ->
      W.vbox [ render_classish_ctxt classish; render_fn_ctxt fn_ctxt ]
  ;;
end

module Ctxt_cont = struct
  let render_local_ctxt local local_rfmts =
    (* We want to render each local variable with the accumulated refinements _and_ the evaluation of those refinements *)
    let init =
      Name.Tm_var.Map.of_alist_exn
      @@ List.map ~f:(fun (tm_var, ty, _spans) -> tm_var, (ty, []))
      @@ Ctxt.Local.bindings local
    in
    let f acc rfmt =
      (* Push each local refinement onto the accumulator for the relavant term var *)
      List.fold_left
        (Ctxt.Local.Refinement.bindings rfmt)
        ~init:acc
        ~f:(fun acc (tm_var, ty_rfmt) ->
          Map.update acc tm_var ~f:(function
            | Some (ty, ty_rfmts) -> ty, ty_rfmt :: ty_rfmts
            | None -> failwith "impossible"))
    in
    let data =
      List.map ~f:(fun (tm_var, (ty, ty_rfmts)) ->
        let refined_ty =
          List.fold_left ty_rfmts ~init:ty ~f:(fun ty rfmt ->
            Ty.refine ty ~rfmt)
        in
        [ Lwd.pure
          @@ W.string ~attr:Attr.(fg yellow)
          @@ Name.Tm_var.to_string tm_var
        ; Ty_view.render ty
        ; W.scrollbox
          @@ W.vlist
          @@ List.map ty_rfmts ~f:Ty_view.render_refinement
        ; Ty_view.render refined_ty
        ])
      @@ Map.to_alist
      @@ List.fold_left local_rfmts ~init ~f
    in
    let headers =
      List.map
        ~f:Lwd.pure
        [ W.string " Name    |  "
        ; W.string "Type    |  "
        ; W.string "Refinements    |  "
        ; W.string "Refined type"
        ]
    in
    W.scrollbox @@ W.grid ~h_space:1 ~headers data
  ;;

  let render_ty_param_ctxt
    (ty_params : Ctxt.Ty_param.t)
    (ty_param_rfmts : Ctxt.Ty_param.Refinement.t list)
    =
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
        List.fold_left
          bounds
          ~init:acc
          ~f:(fun acc (ty_param_nm, ty_param_bound) ->
            Map.update acc ty_param_nm ~f:(function
              | Some (declared_bounds, ty_param_bounds) ->
                declared_bounds, ty_param_bound :: ty_param_bounds
              | None -> failwith "impossible"))
      | `Bottom -> failwith "Founds bottom type parameter refinement"
    in
    let data =
      List.map ~f:(fun (ty_param_name, (declard_bounds, bound_rftms)) ->
        let refined_bounds =
          Ty.Param_bounds.meet_many
            (declard_bounds :: bound_rftms)
            ~prov:Prov.empty
        in
        [ Lwd.pure
          @@ W.string ~attr:Attr.(fg yellow)
          @@ Name.Ty_param.to_string ty_param_name
        ; Ty_view.render_param_bounds declard_bounds
        ; W.scrollbox
          @@ W.vlist
          @@ List.map bound_rftms ~f:Ty_view.render_param_bounds
        ; Ty_view.render_param_bounds refined_bounds
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

  let render ctxt_cont_opt =
    let cont =
      match ctxt_cont_opt with
      | Some ctxt_cont ->
        [ ( "local context"
          , fun _ ->
              render_local_ctxt ctxt_cont.Ctxt.Cont.bindings.local
              @@ List.filter_map ctxt_cont.Ctxt.Cont.rfmtss ~f:(fun rfmt_opt ->
                Option.map rfmt_opt ~f:(fun rfmt ->
                  rfmt.Ctxt.Cont.Refinements.local)) )
        ; ( "type parameter context"
          , fun _ ->
              render_ty_param_ctxt ctxt_cont.Ctxt.Cont.bindings.ty_param
              @@ List.filter_map ctxt_cont.Ctxt.Cont.rfmtss ~f:(fun rfmt_opt ->
                Option.map rfmt_opt ~f:(fun rfmt ->
                  rfmt.Ctxt.Cont.Refinements.ty_param)) )
        ]
      | _ -> []
    in
    match cont with
    | [] -> W.empty_lwd
    | uis -> Tabs.view uis
  ;;
end

module Cont_delta = struct
  let render_local_delta local =
    W.scrollbox
    @@ W.vlist
    @@ List.map ~f:(fun (tm_var, ty, _spans) ->
      W.hbox
        [ Lwd.pure
          @@ W.string ~attr:Attr.(fg yellow)
          @@ Name.Tm_var.to_string tm_var
        ; Helpers.pad ~left:1 ~right:1 @@ Lwd.pure @@ W.string ":"
        ; Ty_view.render ty
        ])
    @@ Ctxt.Local.bindings local
  ;;

  let render_ty_param_delta ty_params =
    W.scrollbox
    @@ W.vlist
    @@ List.map ~f:(fun (name, bounds) ->
      W.hbox
        [ pad ~right:2 @@ Ty_view.render bounds.Ty.Param_bounds.lower
        ; pad ~right:2 @@ Lwd.pure @@ W.string ~attr:Attr.(fg white) "<:"
        ; pad ~right:2
          @@ Lwd.pure
          @@ W.string ~attr:Attr.(fg green ++ st italic)
          @@ Name.Ty_param.to_string name
        ; pad ~right:2 @@ Lwd.pure @@ W.string ~attr:Attr.(fg white) "<:"
        ; Ty_view.render bounds.Ty.Param_bounds.upper
        ])
    @@ Ctxt.Ty_param.bindings ty_params
  ;;

  let render cont_delta =
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
end

module Expr_delta = struct
  let render_local_refinement_delta local =
    W.scrollbox
    @@ W.vlist
    @@ List.map ~f:(fun (name, ty_rfmt) ->
      W.hbox
        [ Lwd.pure
          @@ W.string ~attr:Attr.(fg green)
          @@ Name.Tm_var.to_string name
        ; Lwd.pure @@ Ui.space 1 1
        ; Lwd.pure @@ W.string ~attr:Attr.(fg white) ":"
        ; Lwd.pure @@ Ui.space 3 3
        ; Lwd.pure
          @@ W.string ~attr:Attr.(fg magenta)
          @@ Ty.Refinement.show ty_rfmt
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
               [ pad ~right:1
                 @@ Lwd.pure
                 @@ W.string ~attr:Attr.(fg green ++ st italic)
                 @@ Name.Ty_param.to_string name
               ; pad ~right:2 @@ Lwd.pure @@ W.string ~attr:Attr.(fg white) ":"
               ; pad ~right:1
                 @@ Lwd.pure
                 @@ W.string ~attr:Attr.(fg white) "{ lower: _ ∨"
               ; Ty_view.render lower
               ; pad ~right:1
                 @@ Lwd.pure
                 @@ W.string ~attr:Attr.(fg white) ", upper: _ ∧"
               ; Ty_view.render upper
               ; pad ~left:1 @@ Lwd.pure @@ W.string ~attr:Attr.(fg white) "}"
               ])
           bindings
  ;;

  let render_local_delta local =
    W.scrollbox
    @@ W.vlist
    @@ List.map ~f:(fun (tm_var, ty, _spans) ->
      W.hbox
        [ Lwd.pure
          @@ W.string ~attr:Attr.(fg yellow)
          @@ Name.Tm_var.to_string tm_var
        ; Helpers.pad ~left:1 ~right:1 @@ Lwd.pure @@ W.string ":"
        ; Ty_view.render ty
        ])
    @@ Ctxt.Local.bindings local
  ;;

  let render_ty_param_delta ty_params =
    W.scrollbox
    @@ W.vlist
    @@ List.map ~f:(fun (name, bounds) ->
      W.hbox
        [ pad ~right:2 @@ Ty_view.render bounds.Ty.Param_bounds.lower
        ; pad ~right:2 @@ Lwd.pure @@ W.string ~attr:Attr.(fg white) "<:"
        ; pad ~right:2
          @@ Lwd.pure
          @@ W.string ~attr:Attr.(fg green ++ st italic)
          @@ Name.Ty_param.to_string name
        ; pad ~right:2 @@ Lwd.pure @@ W.string ~attr:Attr.(fg white) "<:"
        ; Ty_view.render bounds.Ty.Param_bounds.upper
        ])
    @@ Ctxt.Ty_param.bindings ty_params
  ;;

  let render expr_delta =
    Tabs.view
      [ ( "local delta"
        , fun _ ->
            match expr_delta.Ctxt.Cont.Expr_delta.bindings with
            | None -> Lwd.pure @@ W.string "(no change)"
            | Some Ctxt.Cont.Bindings.{ local; _ } -> render_local_delta local
        )
      ; ( "local refinement delta"
        , fun _ ->
            match expr_delta.Ctxt.Cont.Expr_delta.rfmts with
            | None -> Lwd.pure @@ W.string "(no change)"
            | Some rfmt_delta ->
              render_local_refinement_delta
                rfmt_delta.Ctxt.Cont.Refinements.local )
      ; ( "type parameter delta"
        , fun _ ->
            match expr_delta.Ctxt.Cont.Expr_delta.bindings with
            | None -> Lwd.pure @@ W.string "(no change)"
            | Some { ty_param; _ } -> render_ty_param_delta ty_param )
      ; ( "type parameter refinement delta"
        , fun _ ->
            match expr_delta.Ctxt.Cont.Expr_delta.rfmts with
            | None -> Lwd.pure @@ W.string "(no change)"
            | Some rfmt_delta ->
              render_ty_param_refinement_delta
                rfmt_delta.Ctxt.Cont.Refinements.ty_param )
      ]
  ;;
end

module Delta = struct
  let render ctxt_delta =
    Tabs.view
      [ ( "next continuation"
        , fun _ ->
            match ctxt_delta.Ctxt.Delta.next with
            | None -> Lwd.pure @@ W.string "(empty)"
            | Some delta -> Cont_delta.render delta )
      ; ( "exit continuation"
        , fun _ ->
            match ctxt_delta.Ctxt.Delta.exit with
            | None -> Lwd.pure @@ W.string "(empty)"
            | Some delta -> Cont_delta.render delta )
      ]
  ;;
end

module Ty_param_refinement = struct
  let render ty_params =
    let render_bounds bounds =
      List.map bounds ~f:(fun (name, bounds) ->
        W.hbox
          [ pad ~right:2 @@ Ty_view.render bounds.Ty.Param_bounds.lower
          ; pad ~right:2 @@ Lwd.pure @@ W.string ~attr:Attr.(fg white) "<:"
          ; pad ~right:2
            @@ Lwd.pure
            @@ W.string ~attr:Attr.(fg green ++ st italic)
            @@ Name.Ty_param.to_string name
          ; pad ~right:2 @@ Lwd.pure @@ W.string ~attr:Attr.(fg white) "<:"
          ; Ty_view.render bounds.Ty.Param_bounds.upper
          ])
    in
    match Ctxt.Ty_param.Refinement.bindings ty_params with
    | `Bottom -> [ Lwd.pure @@ W.string "(bottom)" ]
    | `Top -> [ Lwd.pure @@ W.string "(top)" ]
    | `Bounds bounds -> render_bounds bounds
  ;;
end

module Cstr = struct
  let render t =
    match t with
    | Subtyping.Cstr.Is_subtype { ty_sub; ty_super } ->
      W.hbox
        [ Ty_view.render ty_sub
        ; pad ~left:1 ~right:1 @@ Lwd.pure @@ W.string "<:"
        ; Ty_view.render ty_super
        ]
  ;;
end

module Prop = struct
  let rec render t =
    match t with
    | Subtyping.Prop.Atom cstr -> Cstr.render cstr
    | Subtyping.Prop.Conj [] -> Lwd.pure @@ W.string "T"
    | Subtyping.Prop.Conj props ->
      W.flex_box
        [ Lwd.pure @@ W.string "("
        ; W.flex_box
          @@ List.intersperse ~sep:(Lwd.pure @@ W.string " & ")
          @@ List.map ~f:render props
        ; Lwd.pure @@ W.string "("
        ]
    | Subtyping.Prop.Disj [] -> Lwd.pure @@ W.string "F"
    | Subtyping.Prop.Disj props ->
      W.flex_box
        [ Lwd.pure @@ W.string "("
        ; W.flex_box
          @@ List.intersperse ~sep:(Lwd.pure @@ W.string " | ")
          @@ List.map ~f:render props
        ; Lwd.pure @@ W.string ")"
        ]
  ;;
end

module Variance = struct
  let render t =
    Lwd.pure
    @@ W.string ~attr:Attr.(st bold)
    @@
    match t with
    | Common.Variance.Contrav -> "-"
    | Common.Variance.Cov -> "+"
    | Common.Variance.Inv -> "o"
  ;;
end

module Instantiation = struct
  let render inst =
    match inst with
    | Oracle.Classish.Not_a_subclass -> Lwd.pure @@ W.string "Not a sublass"
    | Oracle.Classish.Direct ty_args ->
      W.hbox
        ((Helpers.pad ~right:1 @@ Lwd.pure @@ W.string "Direct sublass:")
         :: List.map ty_args ~f:Ty_view.render)
    | Oracle.Classish.Transitive ty_args ->
      W.hbox
        ((Helpers.pad ~right:1 @@ Lwd.pure @@ W.string "Transitive sublass:")
         :: List.map ty_args ~f:Ty_view.render)
  ;;
end

module Status = struct
  let render_comp name =
    Helpers.pad ~bottom:1
    @@ Lwd.pure
    @@ W.string ~attr:Attr.(st underline ++ fg cyan) name
  ;;

  let render_status_desc desc =
    Helpers.pad ~bottom:1 @@ Lwd.pure @@ W.string ~attr:Attr.(st italic) desc
  ;;

  let render_typing status =
    let open Debugging.Status.Typing_status in
    let status_ui =
      match status with
      | Logged_error { data; _ } ->
        W.vbox
          [ render_status_desc "Logged an error"
          ; Lwd.pure @@ W.string @@ Typing.Err.show data
          ]
      | Logged_warning { data; _ } ->
        W.vbox
          [ render_status_desc "Logged a warning"
          ; Lwd.pure @@ W.string @@ Typing.Warn.show data
          ]
      | Logged_enter_classish_def
          { data = { classish_def = { elem; _ }; _ }; _ } ->
        W.vbox
          [ render_status_desc "Entered classish def"
          ; W.hbox
              [ Helpers.pad ~right:1 @@ Lwd.pure @@ W.string "name:"
              ; Lwd.pure
                @@ W.string
                @@ Name.Ctor.to_string
                @@ Located.elem elem.name
              ]
          ; W.hbox
              [ Helpers.pad ~right:1 @@ Lwd.pure @@ W.string "kind:"
              ; Lwd.pure
                @@ W.string
                @@ Lang.Classish_def.Kind.to_string
                @@ Located.elem elem.kind
              ]
          ]
      | Logged_exit_classish_def _ -> render_status_desc "Exited classish def"
      | Logged_enter_fn_def { data = { fn_def = { elem; _ }; _ }; _ } ->
        W.vbox
          [ render_status_desc "Entered function def"
          ; W.hbox
              [ Helpers.pad ~right:1 @@ Lwd.pure @@ W.string "name:"
              ; Lwd.pure
                @@ W.string
                @@ Name.Fn.to_string
                @@ Located.elem elem.name
              ]
          ; W.hbox
              [ Helpers.pad ~right:1 @@ Lwd.pure @@ W.string "return:"
              ; Ty_view.render elem.lambda.lambda_sig.elem.return
              ]
          ]
      | Logged_exit_fn_def _ -> render_status_desc "Exited function def"
      | Logged_enter_synth_expr _ ->
        W.vbox [ render_status_desc "Entered expr synth" ]
      | Logged_enter_check_expr { data; _ } ->
        W.vbox
          [ render_status_desc "Entered expr check"
          ; W.hbox
              [ Helpers.pad ~right:1 @@ Lwd.pure @@ W.string "checking against:"
              ; Ty_view.render data.against
              ]
          ]
      | Logged_exit_expr { data; _ } ->
        W.vbox
          [ render_status_desc "Exited expr"
          ; W.hbox
              [ Helpers.pad ~right:1 @@ Lwd.pure @@ W.string "type:"
              ; Ty_view.render data.ty
              ]
          ; Lwd.pure @@ W.string "expression delta:"
          ; Expr_delta.render data.expr_delta
          ]
      | Logged_enter_stmt _ -> W.vbox [ render_status_desc "Entered stmt" ]
      | Logged_exit_stmt { data; _ } ->
        W.vbox
          [ render_status_desc "Exited stmt"
          ; Lwd.pure @@ W.string "delta:"
          ; Delta.render data.delta
          ]
    in
    W.vbox [ render_comp "Typing"; status_ui ]
  ;;

  let render_subtyping_err err =
    Lwd.pure @@ W.string @@ Subtyping.Err.to_string err
  ;;

  let render_subtyping status =
    let open Debugging.Status.Subtyping_status in
    let status_ui =
      match status with
      | Logged_enter_tell_prop { data; _ } ->
        W.vbox
          [ render_status_desc "Entered tell prop"
          ; W.hbox
              [ pad ~right:1 @@ Lwd.pure @@ W.string "prop:"
              ; Prop.render data.prop
              ]
          ]
      | Logged_enter_tell_cstr { data; _ } ->
        W.vbox
          [ render_status_desc "Entered tell cstr"
          ; W.hbox
              [ pad ~right:1 @@ Lwd.pure @@ W.string "cstr:"
              ; Cstr.render data.cstr
              ]
          ]
      | Logged_enter_tell_all { data; _ } ->
        W.vbox
          [ render_status_desc "Entered tell all"
          ; W.hbox
              [ W.vbox
                  ((Lwd.pure @@ W.string "props:")
                   :: List.map ~f:Prop.render data.props)
              ; Helpers.pad ~left:1
                @@ W.vbox
                     ((Lwd.pure @@ W.string "errors:")
                      :: List.map ~f:render_subtyping_err data.errs)
              ]
          ]
      | Logged_enter_tell_any { data; _ } ->
        W.vbox
          [ render_status_desc "Entered tell any"
          ; W.hbox
              [ W.vbox
                  ((Lwd.pure @@ W.string "props:")
                   :: List.map ~f:Prop.render data.props)
              ; Helpers.pad ~left:1
                @@ W.vbox
                     ((Lwd.pure @@ W.string "errors:")
                      :: List.map ~f:render_subtyping_err data.errs)
              ]
          ]
      | Logged_exit_tell { data = { tell; err_opt }; _ } ->
        let msg =
          Format.sprintf {|Exited tell %s|} @@ Subtyping.Eff.show_tell tell
        in
        W.vbox
          [ render_status_desc msg
          ; W.hbox
              [ pad ~right:1 @@ Lwd.pure @@ W.string "error:"
              ; Option.value_map
                  ~default:(Lwd.pure @@ W.string "(no error)")
                  ~f:render_subtyping_err
                  err_opt
              ]
          ]
      | Asked_up { data = { of_; at }; _ } ->
        W.vbox
          [ render_status_desc "Asked up"
          ; W.hbox
              [ pad ~right:1 @@ Lwd.pure @@ W.string "of:"
              ; Ty_view.render_ctor of_
              ]
          ; W.hbox
              [ pad ~right:1 @@ Lwd.pure @@ W.string "at:"
              ; Lwd.pure @@ W.string @@ Name.Ctor.to_string at
              ]
          ]
      | Answered_up { data = inst; _ } ->
        W.vbox [ render_status_desc "Answered up"; Instantiation.render inst ]
      | Asked_ty_param_variances { data; _ } ->
        W.vbox
          [ render_status_desc "Asked variance"
          ; W.hbox
              [ pad ~right:1 @@ Lwd.pure @@ W.string "ctor:"
              ; Lwd.pure @@ W.string @@ Name.Ctor.to_string data
              ]
          ]
      | Answered_ty_param_variances { data = Some vs; _ } ->
        W.vbox
          [ render_status_desc "Answered up"
          ; W.vbox
              ((pad ~right:1 @@ Lwd.pure @@ W.string "args:")
               :: List.map
                    ~f:(fun Located.{ elem; _ } -> Variance.render elem)
                    vs)
          ]
      | Answered_ty_param_variances _ ->
        W.vbox
          [ render_status_desc "Answered up"
          ; Lwd.pure @@ W.string "(unknown ctor)"
          ]
    in
    W.vbox [ render_comp "Subtyping"; status_ui ]
  ;;

  let render_refinement status =
    let open Debugging.Status.Refinement_status in
    let status_ui =
      match status with
      | Logged_enter_refinement { data; _ } ->
        W.vbox
          [ render_status_desc "Entered refinement"
          ; W.hbox
              [ pad ~right:1 @@ Lwd.pure @@ W.string "scrut:"
              ; Ty_view.render data.ty_scrut
              ]
          ; W.hbox
              [ pad ~right:1 @@ Lwd.pure @@ W.string "test:"
              ; Ty_view.render data.ty_test
              ]
          ]
      | Logged_enter_ty { data; _ } ->
        W.vbox
          [ render_status_desc "Entered ty"
          ; W.hbox
              [ pad ~right:1 @@ Lwd.pure @@ W.string "scrut:"
              ; Ty_view.render data.ty_scrut
              ]
          ; W.hbox
              [ pad ~right:1 @@ Lwd.pure @@ W.string "test:"
              ; Ty_view.render data.ty_test
              ]
          ]
      | Logged_enter_existential_scrut { data; _ } ->
        W.vbox
          [ render_status_desc "Entered existential (scrut)"
          ; W.hbox
              [ pad ~right:1 @@ Lwd.pure @@ W.string "scrut:"
              ; Ty_view.render_exists data.ty_exists
              ]
          ; W.hbox
              [ pad ~right:1 @@ Lwd.pure @@ W.string "test:"
              ; Ty_view.render data.ty_test
              ]
          ]
      | Logged_enter_existential_test { data; _ } ->
        W.vbox
          [ render_status_desc "Entered existential (test)"
          ; W.hbox
              [ pad ~right:1 @@ Lwd.pure @@ W.string "scrut:"
              ; Ty_view.render data.ty_scrut
              ]
          ; W.hbox
              [ pad ~right:1 @@ Lwd.pure @@ W.string "test:"
              ; Ty_view.render_exists data.ty_exists
              ]
          ]
      | Logged_enter_union_scrut { data; _ } ->
        W.vbox
          [ render_status_desc "Entered union (scrut)"
          ; W.hbox
              [ pad ~right:1 @@ Lwd.pure @@ W.string "scrut:"
              ; W.flex_box @@ List.map ~f:Ty_view.render data.tys_scrut
              ]
          ; W.hbox
              [ pad ~right:1 @@ Lwd.pure @@ W.string "test:"
              ; Ty_view.render data.ty_test
              ]
          ]
      | Logged_enter_inter_scrut { data; _ } ->
        W.vbox
          [ render_status_desc "Entered inter (scrut)"
          ; W.hbox
              [ pad ~right:1 @@ Lwd.pure @@ W.string "scrut:"
              ; W.flex_box @@ List.map ~f:Ty_view.render data.tys_scrut
              ]
          ; W.hbox
              [ pad ~right:1 @@ Lwd.pure @@ W.string "test:"
              ; Ty_view.render data.ty_test
              ]
          ]
      | Logged_enter_union_test { data; _ } ->
        W.vbox
          [ render_status_desc "Entered union (test)"
          ; W.hbox
              [ pad ~right:1 @@ Lwd.pure @@ W.string "scrut:"
              ; Ty_view.render data.ty_scrut
              ]
          ; W.hbox
              [ pad ~right:1 @@ Lwd.pure @@ W.string "test:"
              ; W.flex_box @@ List.map ~f:Ty_view.render data.tys_test
              ]
          ]
      | Logged_enter_inter_test { data; _ } ->
        W.vbox
          [ render_status_desc "Entered inter (test)"
          ; W.hbox
              [ pad ~right:1 @@ Lwd.pure @@ W.string "scrut:"
              ; Ty_view.render data.ty_scrut
              ]
          ; W.hbox
              [ pad ~right:1 @@ Lwd.pure @@ W.string "test:"
              ; W.flex_box @@ List.map ~f:Ty_view.render data.tys_test
              ]
          ]
      | Logged_enter_top_level_generic_scrut { data; _ } ->
        W.vbox
          [ render_status_desc "Entered top-level generic (scrut)"
          ; W.hbox
              [ pad ~right:1 @@ Lwd.pure @@ W.string "scrut:"
              ; Lwd.pure @@ W.string @@ Name.Ty_param.to_string data.name_scrut
              ]
          ; W.hbox
              [ pad ~right:1 @@ Lwd.pure @@ W.string "test:"
              ; Ty_view.render data.ty_test
              ]
          ]
      | Logged_enter_top_level_generic_test { data; _ } ->
        W.vbox
          [ render_status_desc "Entered top-level generic (test)"
          ; W.hbox
              [ pad ~right:1 @@ Lwd.pure @@ W.string "scrut:"
              ; Ty_view.render data.ty_scrut
              ]
          ; W.hbox
              [ pad ~right:1 @@ Lwd.pure @@ W.string "test:"
              ; Lwd.pure @@ W.string @@ Name.Ty_param.to_string data.name_test
              ]
          ]
      | Logged_enter_ctor { data; _ } ->
        W.vbox
          [ render_status_desc "Entered ctor"
          ; W.hbox
              [ pad ~right:1 @@ Lwd.pure @@ W.string "scrut:"
              ; Ty_view.render_ctor data.ctor_scrut
              ]
          ; W.hbox
              [ pad ~right:1 @@ Lwd.pure @@ W.string "test:"
              ; Ty_view.render_ctor data.ctor_test
              ]
          ]
      | Logged_enter_ctor_arg { data; _ } ->
        W.vbox
          [ render_status_desc "Entered ctor arg"
          ; W.hbox
              [ pad ~right:1 @@ Lwd.pure @@ W.string "scrut:"
              ; Ty_view.render data.ty_scrut
              ]
          ; W.hbox
              [ pad ~right:1 @@ Lwd.pure @@ W.string "test:"
              ; Ty_view.render data.ty_test
              ]
          ]
      | Asked_up { data = { of_; at }; _ } ->
        W.vbox
          [ render_status_desc "Asked up"
          ; W.hbox
              [ pad ~right:1 @@ Lwd.pure @@ W.string "of:"
              ; Ty_view.render_ctor of_
              ]
          ; W.hbox
              [ pad ~right:1 @@ Lwd.pure @@ W.string "at:"
              ; Lwd.pure @@ W.string @@ Name.Ctor.to_string at
              ]
          ]
      | Answered_up { data = inst; _ } ->
        W.vbox [ render_status_desc "Answered up"; Instantiation.render inst ]
      | Asked_ty_param_variance { data; _ } ->
        W.vbox
          [ render_status_desc "Asked variance"
          ; W.hbox
              [ pad ~right:1 @@ Lwd.pure @@ W.string "ctor:"
              ; Lwd.pure @@ W.string @@ Name.Ctor.to_string data
              ]
          ]
      | Answered_ty_param_variance { data = Some vs; _ } ->
        W.vbox
          [ render_status_desc "Answered up"
          ; W.vbox
              ((pad ~right:1 @@ Lwd.pure @@ W.string "args:")
               :: List.map
                    ~f:(fun Located.{ elem; _ } -> Variance.render elem)
                    vs)
          ]
      | Answered_ty_param_variance _ ->
        W.vbox
          [ render_status_desc "Answered up"
          ; Lwd.pure @@ W.string "(unknown ctor)"
          ]
      | Requested_fresh_ty_params { data; _ } ->
        W.vbox
          [ render_status_desc "Requested fresh ty params"
          ; W.hbox
              [ pad ~right:1 @@ Lwd.pure @@ W.string "number:"
              ; Lwd.pure @@ W.string @@ Int.to_string data
              ]
          ]
      | Received_fresh_ty_params { data; _ } ->
        W.vbox
          [ render_status_desc "Received fresh ty params"
          ; W.hbox
              ((pad ~right:1 @@ Lwd.pure @@ W.string "names:")
               :: List.map data ~f:(fun name ->
                 Lwd.pure @@ W.string @@ Name.Ty_param.to_string name))
          ]
      | Logged_exit { data = { elem; ty_rfmt; ty_param_rfmt_opt }; _ } ->
        let msg =
          Format.sprintf {|Exited %s|}
          @@ String.lowercase
          @@ Refinement.Eff.show_elem elem
        in
        W.vbox
          [ render_status_desc msg
          ; W.hbox
              [ pad ~right:1 @@ Lwd.pure @@ W.string "type refinement:"
              ; Ty_view.render_refinement ty_rfmt
              ]
          ; W.vbox
              ((pad ~right:1 @@ Lwd.pure @@ W.string "type param refinement:")
               :: Option.value_map
                    ty_param_rfmt_opt
                    ~default:[]
                    ~f:(fun (_, ty_param) ->
                      Ty_param_refinement.render ty_param))
          ]
    in
    W.vbox [ render_comp "Refinement"; status_ui ]
  ;;

  let render_exposure status =
    let open Debugging.Status.Exposure_status in
    let status_ui =
      match status with
      | Asked_up { data = { of_; at }; _ } ->
        W.vbox
          [ render_status_desc "Asked up"
          ; W.hbox
              [ pad ~right:1 @@ Lwd.pure @@ W.string "of:"
              ; Ty_view.render_ctor of_
              ]
          ; W.hbox
              [ pad ~right:1 @@ Lwd.pure @@ W.string "at:"
              ; Lwd.pure @@ W.string @@ Name.Ctor.to_string at
              ]
          ]
      | Answered_up { data = inst; _ } ->
        W.vbox [ render_status_desc "Answered up"; Instantiation.render inst ]
      | _ -> W.empty_lwd
    in
    W.vbox [ render_comp "Exposure"; status_ui ]
  ;;

  let render status =
    let open Debugging.Status in
    Helpers.pad ~top:1 ~left:1
    @@
    match status with
    | Completed ->
      Lwd.pure @@ W.string ~attr:Attr.(st bold ++ fg green) "Completed"
    | Failed exn ->
      W.vbox
        [ Lwd.pure @@ W.string ~attr:Attr.(st bold ++ fg red) "Failed"
        ; Lwd.pure @@ W.string @@ Exn.to_string exn
        ]
    | Typing status -> render_typing status
    | Subtyping status -> render_subtyping status
    | Refinement status -> render_refinement status
    | Exposure status -> render_exposure status
  ;;
end
