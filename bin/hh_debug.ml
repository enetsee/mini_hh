open Core
open Reporting
open Nottui
module W = Nottui_widgets
module Attr = Notty.A

let pad ?(top = 0) ?(left = 0) ?(bottom = 0) ?(right = 0) ui =
  W.hbox
    [ Lwd.pure @@ Ui.space left 0
    ; W.vbox [ Lwd.pure @@ Ui.space 0 top; ui; Lwd.pure @@ Ui.space 0 bottom ]
    ; Lwd.pure @@ Ui.space right 0
    ]
;;

module File_select = struct
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
          if fold then W.unfoldable ~folded_by_default:true (Lwd.return @@ W.string @@ path ^ "/") ui else ui ()
        | _ ->
          let basename = Filename.basename path in
          Lwd.return @@ W.button ~attr:Notty.A.(st underline ++ fg blue) basename (fun () -> on_select path)
      with
      | e ->
        Lwd.return
        @@ Ui.vcat [ W.printf ~attr:Notty.A.(bg red) "cannot list directory %s" path; W.string @@ Exn.to_string e ]
    in
    aux ~fold:false path
  ;;
end

module Button = struct
  let view ~label ~on_click ~enabled =
    let ln = String.length label + 2 in
    let hline = String.concat @@ List.init ln ~f:(fun _ -> "═") in
    let top = "╔" ^ hline ^ "╗" in
    let bottom = "╚" ^ hline ^ "╝" in
    let left, right = "║ ", " ║" in
    let attr_surround = if enabled then Attr.(st bold ++ fg white) else Attr.(st bold ++ fg (gray 4))
    and attr_label = if enabled then Attr.(st underline ++ fg blue) else Attr.(fg (gray 10)) in
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
    Ui.mouse_area handler (Ui.vcat [ ui_top; Ui.hcat [ ui_left; ui_label; ui_right ]; ui_bottom ])
  ;;
end

module Tabs = struct
  open Lwd.Infix
  open Nottui

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

  let view (tabs : (string * (unit -> Ui.t Lwd.t)) list) : Ui.t Lwd.t =
    match tabs with
    | [] -> Lwd.return Ui.empty
    | _ ->
      let cur = Lwd.var 0 in
      Lwd.bind (Lwd.get cur) ~f:(fun idx_sel ->
        let _, f = List.nth_exn tabs idx_sel in
        let tab_bar =
          tabs
          |> List.mapi ~f:(fun i (s, _) ->
            let tab_annot = if i = idx_sel then render_tab_active s else render_tab s in
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
end

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

let cursor_l = "»"
let cursor_r = "«"
(* ~~ State ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)

let st_file : string option Lwd.var = Lwd.var None

let st_source =
  Lwd.map (Lwd.get st_file) ~f:(fun file_opt ->
    match file_opt with
    | Some file -> In_channel.read_lines file
    | _ -> logo)
;;

let st_prog =
  Lwd.map
    (Lwd.get st_file)
    ~f:(Option.map ~f:(fun file -> Lang.Prog.elab_to_generic @@ Source.Parse.parse_file_exn file))
;;

let st_oracle, st_decl_errs =
  let pair = Lwd.map st_prog ~f:(Option.map ~f:Oracle.of_program) in
  let fst = Lwd.map pair ~f:(Option.map ~f:fst)
  and snd = Lwd.map pair ~f:(Option.map ~f:snd) in
  fst, snd
;;

type rfmt_request =
  | Refine_ty of
      { ty_scrut : Ty.t
      ; ty_test : Ty.t
      }
  | Refine_existential_scrut of
      { ty_exists : Ty.Exists.t
      ; ty_test : Ty.t
      }
  | Refine_existential_test of
      { ty_exists : Ty.Exists.t
      ; ty_scrut : Ty.t
      }
  | Refine_union_scrut of
      { tys_scrut : Ty.t list
      ; ty_test : Ty.t
      }
  | Refine_union_test of
      { tys_test : Ty.t list
      ; ty_scrut : Ty.t
      }

type status_payload =
  | Expr_delta of Span.t * Ty.t * Ctxt.Cont.Expr_delta.t
  | Stmt_delta of Ctxt.Delta.t
  | Rfmt_request of rfmt_request
  | Rfmt of Ty.Refinement.t * (Prov.t * Ctxt.Ty_param.Refinement.t) option
  | Asked_up of
      { of_ : Ty.Ctor.t
      ; at : Name.Ctor.t
      }
  | Asked_ctor_info of Name.Ctor.t
  | Asked_ty_param_variances of Name.Ctor.t
  | Raised_error of Typing.Err.t
  | Raised_warning of Typing.Warn.t
  | Span of Span.t
  | Empty
  | Complete
  | Failed of Exn.t

let st_defs = Lwd.map st_prog ~f:(Option.value_map ~default:[] ~f:(fun Lang.Prog.{ defs } -> defs))
let st_current_def : Lang.Def.t option Lwd.var = Lwd.var None
let st_step : Typing.Eff.Debug.Step.t option Lwd.var = Lwd.var None
let st_span : Span.t option Lwd.var = Lwd.var None
let st_ctxt_def : Ctxt.Def.t option Lwd.var = Lwd.var None
let st_ctxt_cont : Ctxt.Cont.t option Lwd.var = Lwd.var None
let st_status_name : string option Lwd.var = Lwd.var None
let st_status_payload : status_payload option Lwd.var = Lwd.var None

let update_step step =
  let open Typing.Eff.Debug.Status in
  match Typing.Eff.Debug.Step.status step with
  (* ~~ Entry ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
  | Entered_expr { ctxt_def; ctxt_cont; span; _ } ->
    let _ : unit = Lwd.set st_span @@ Some span in
    let _ : unit = Lwd.set st_ctxt_def @@ Some ctxt_def
    and _ : unit = Lwd.set st_ctxt_cont @@ Some ctxt_cont
    and _ : unit = Lwd.set st_status_name @@ Some "entered expression"
    and _ : unit = Lwd.set st_status_payload @@ Some (Span span) in
    ()
  | Entered_stmt { ctxt_def; ctxt_cont; span; _ } ->
    let _ : unit = Lwd.set st_span @@ Some span in
    let _ : unit = Lwd.set st_ctxt_def @@ Some ctxt_def
    and _ : unit = Lwd.set st_ctxt_cont @@ Some ctxt_cont
    and _ : unit = Lwd.set st_status_name @@ Some "entered statement"
    and _ : unit = Lwd.set st_status_payload @@ Some (Span span) in
    ()
  | Entered_classish_def { ctxt_def; ctxt_cont; span; _ } ->
    let _ : unit = Lwd.set st_span @@ Some span in
    let _ : unit = Lwd.set st_ctxt_def @@ Some ctxt_def
    and _ : unit = Lwd.set st_ctxt_cont @@ Some ctxt_cont
    and _ : unit = Lwd.set st_status_name @@ Some "entered class(ish) definition"
    and _ : unit = Lwd.set st_status_payload @@ Some (Span span) in
    ()
  | Entered_fn_def { ctxt_def; ctxt_cont; span; _ } ->
    let _ : unit = Lwd.set st_span @@ Some span in
    let _ : unit = Lwd.set st_ctxt_def @@ Some ctxt_def
    and _ : unit = Lwd.set st_ctxt_cont @@ Some ctxt_cont
    and _ : unit = Lwd.set st_status_name @@ Some "entered function definition"
    and _ : unit = Lwd.set st_status_payload @@ Some (Span span) in
    ()
  | Entered_refinement { ty_test; ty_scrut; ctxt_cont; _ } ->
    let _ : unit = Lwd.set st_ctxt_cont @@ Some ctxt_cont
    and _ : unit = Lwd.set st_status_name @@ Some "entered refinement"
    and _ : unit = Lwd.set st_status_payload @@ Some (Rfmt_request (Refine_ty { ty_scrut; ty_test })) in
    ()
  | Entered_refine_ty { ty_test; ty_scrut; ctxt_cont; _ } ->
    let _ : unit = Lwd.set st_ctxt_cont @@ Some ctxt_cont
    and _ : unit = Lwd.set st_status_name @@ Some "entered refine type"
    and _ : unit = Lwd.set st_status_payload @@ Some (Rfmt_request (Refine_ty { ty_scrut; ty_test })) in
    ()
  | Entered_refine_existential_scrut { ty_exists; ty_test; ctxt_cont; _ } ->
    let _ : unit = Lwd.set st_ctxt_cont @@ Some ctxt_cont
    and _ : unit = Lwd.set st_status_name @@ Some "entered refine existential scrutinee"
    and _ : unit = Lwd.set st_status_payload @@ Some (Rfmt_request (Refine_existential_scrut { ty_exists; ty_test })) in
    ()
  | Entered_refine_existential_test { ty_exists; ty_scrut; ctxt_cont; _ } ->
    let _ : unit = Lwd.set st_ctxt_cont @@ Some ctxt_cont
    and _ : unit = Lwd.set st_status_name @@ Some "entered refine existential test"
    and _ : unit = Lwd.set st_status_payload @@ Some (Rfmt_request (Refine_existential_test { ty_exists; ty_scrut })) in
    ()
  | Entered_refine_union_scrut { tys_scrut; ty_test; ctxt_cont; _ } ->
    let _ : unit = Lwd.set st_ctxt_cont @@ Some ctxt_cont
    and _ : unit = Lwd.set st_status_name @@ Some "entered refine union scrutinee"
    and _ : unit = Lwd.set st_status_payload @@ Some (Rfmt_request (Refine_union_scrut { tys_scrut; ty_test })) in
    ()
  | Entered_refine_union_test { tys_test; ty_scrut; ctxt_cont; _ } ->
    let _ : unit = Lwd.set st_ctxt_cont @@ Some ctxt_cont
    and _ : unit = Lwd.set st_status_name @@ Some "entered refine union test"
    and _ : unit = Lwd.set st_status_payload @@ Some (Rfmt_request (Refine_union_test { tys_test; ty_scrut })) in
    ()
  | Asked_ctor { name; _ } ->
    let _ : unit = Lwd.set st_status_name @@ Some "asked for type parmeter and superclass information"
    and _ : unit = Lwd.set st_status_payload @@ Some (Asked_ctor_info name) in
    ()
  | Asked_up { of_; at; _ } ->
    let _ : unit = Lwd.set st_status_name @@ Some "asked for constructor type instantiation at superclass"
    and _ : unit = Lwd.set st_status_payload @@ Some (Asked_up { of_; at }) in
    ()
  | Asked_ty_param_variances { ctor; _ } ->
    let _ : unit = Lwd.set st_status_name @@ Some "asked for type parmeter variance information"
    and _ : unit = Lwd.set st_status_payload @@ Some (Asked_ty_param_variances ctor) in
    ()
  | Requested_fresh_ty_params _ ->
    let _ : unit = Lwd.set st_status_name @@ Some "asked for fresh type parameter names"
    and _ : unit = Lwd.set st_status_payload @@ Some Empty in
    ()
  (* ~~ Exit ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
  | Exited_expr { span; ty; expr_delta; _ } ->
    let _ : unit = Lwd.set st_span @@ Some span in
    let _ : unit = Lwd.set st_status_name @@ Some "exited expression"
    and _ : unit = Lwd.set st_status_payload @@ Some (Expr_delta (span, ty, expr_delta)) in
    ()
  | Exited_stmt { delta; span; _ } ->
    let _ : unit = Lwd.set st_span @@ Some span in
    let _ : unit = Lwd.set st_status_name @@ Some "exited statement"
    and _ : unit = Lwd.set st_status_payload @@ Some (Stmt_delta delta) in
    ()
  | Exited_classish_def _ ->
    let _ : unit = Lwd.set st_status_name @@ Some "exited class(ish) definition"
    and _ : unit = Lwd.set st_status_payload @@ Some Empty in
    ()
  | Exited_fn_def _ ->
    let _ : unit = Lwd.set st_status_name @@ Some "exited function definition"
    and _ : unit = Lwd.set st_status_payload @@ Some Empty in
    ()
  | Raised_error { err; _ } ->
    let _ : unit = Lwd.set st_status_name @@ Some "raised an error"
    and _ : unit = Lwd.set st_status_payload @@ Some (Raised_error err) in
    ()
  | Raised_warning { warn; _ } ->
    let _ : unit = Lwd.set st_status_name @@ Some "raised a warning"
    and _ : unit = Lwd.set st_status_payload @@ Some (Raised_warning warn) in
    ()
  | Exited_refinement { ty_rfmt; ty_param_rfmt_opt; _ } ->
    let _ : unit = Lwd.set st_status_name @@ Some "exited refinement"
    and _ : unit = Lwd.set st_status_payload @@ Some (Rfmt (ty_rfmt, ty_param_rfmt_opt)) in
    ()
  | Exited_refine_ty { ty_rfmt; ty_param_rfmt_opt; _ } ->
    let _ : unit = Lwd.set st_status_name @@ Some "exited refine type"
    and _ : unit = Lwd.set st_status_payload @@ Some (Rfmt (ty_rfmt, ty_param_rfmt_opt)) in
    ()
  | Exited_refine_existential_scrut { ty_rfmt; ty_param_rfmt_opt; _ } ->
    let _ : unit = Lwd.set st_status_name @@ Some "exited refine existential scrutinee"
    and _ : unit = Lwd.set st_status_payload @@ Some (Rfmt (ty_rfmt, ty_param_rfmt_opt)) in
    ()
  | Exited_refine_existential_test { ty_rfmt; ty_param_rfmt_opt; _ } ->
    let _ : unit = Lwd.set st_status_name @@ Some "exited refine existential test"
    and _ : unit = Lwd.set st_status_payload @@ Some (Rfmt (ty_rfmt, ty_param_rfmt_opt)) in
    ()
  | Exited_refine_union_scrut { ty_rfmt; ty_param_rfmt_opt; _ } ->
    let _ : unit = Lwd.set st_status_name @@ Some "exited refine union scrutinee"
    and _ : unit = Lwd.set st_status_payload @@ Some (Rfmt (ty_rfmt, ty_param_rfmt_opt)) in
    ()
  | Exited_refine_union_test { ty_rfmt; ty_param_rfmt_opt; _ } ->
    let _ : unit = Lwd.set st_status_name @@ Some "exited refine union test"
    and _ : unit = Lwd.set st_status_payload @@ Some (Rfmt (ty_rfmt, ty_param_rfmt_opt)) in
    ()
  | Complete ->
    let _ : unit = Lwd.set st_status_name @@ Some "exited typing"
    and _ : unit = Lwd.set st_status_payload @@ Some Complete in
    ()
  | Failed exn ->
    let _ : unit = Lwd.set st_status_name @@ Some "failed typing"
    and _ : unit = Lwd.set st_status_payload @@ Some (Failed exn) in
    ()
;;

let move_next ~oracle () =
  let step_opt = Lwd.peek st_step in
  let step = Option.map2 step_opt oracle ~f:(fun step oracle -> Typing.Eff.Debug.Step.next step ~oracle) in
  (* Some steps will give us the updated continuation and definition contexts; if the new step does we update
     the current continuation context and current definition context *)
  let _ : unit = Option.iter step ~f:update_step in
  let _ : unit = Lwd.set st_step step in
  ()
;;

(* ~~ UI elements ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)

(* ~~ Type rendering ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)

let render_base base = Lwd.pure @@ W.string ~attr:Attr.(fg blue) @@ Common.Base.to_string base

let rec render_ty t =
  let open Ty.Node in
  match t.Ty.node with
  | Base base -> render_base base
  | Generic name -> Lwd.pure @@ W.string ~attr:Attr.(fg green ++ st italic) @@ Name.Ty_param.to_string name
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
    ; W.hbox @@ List.intersperse ~sep:(pad ~left:1 ~right:1 @@ Lwd.pure @@ W.string "|") @@ List.map tys ~f:render_ty
    ; Lwd.pure @@ W.string ")"
    ]

and render_intersection tys =
  W.hbox
    [ Lwd.pure @@ W.string "("
    ; W.hbox @@ List.intersperse ~sep:(pad ~left:1 ~right:1 @@ Lwd.pure @@ W.string "&") @@ List.map tys ~f:render_ty
    ; Lwd.pure @@ W.string ")"
    ]

and render_tuple Ty.Tuple.{ required; optional; variadic } =
  let sep = pad ~left:1 ~right:1 @@ Lwd.pure @@ W.string "," in
  let req = W.hbox @@ List.intersperse ~sep @@ List.map required ~f:render_ty
  and optional =
    match optional with
    | [] -> W.empty_lwd
    | _ ->
      W.hbox
      @@ (sep
          :: (List.intersperse ~sep
              @@ List.map optional ~f:(fun ty ->
                W.hbox [ pad ~right:1 @@ Lwd.pure @@ W.string "optional"; render_ty ty ])))
  and variadic =
    Option.value_map variadic ~default:W.empty_lwd ~f:(fun ty ->
      W.hbox [ sep; Lwd.pure @@ W.string "..."; render_ty ty ])
  in
  let elems = W.hbox [ req; optional; variadic ] in
  W.hbox [ pad ~right:1 @@ Lwd.pure @@ W.string "("; elems; pad ~left:1 @@ Lwd.pure @@ W.string ")" ]

and render_fn Ty.Fn.{ params; return } =
  W.hbox
    [ Lwd.pure @@ W.string "("
    ; render_tuple params
    ; pad ~right:1 @@ Lwd.pure @@ W.string ":"
    ; render_ty return
    ; Lwd.pure @@ W.string ")"
    ]

and render_ctor Ty.Ctor.{ name; args } =
  match args with
  | [] -> Lwd.pure @@ W.string ~attr:Attr.(fg lightcyan) @@ Name.Ctor.to_string name
  | _ ->
    W.hbox
      [ Lwd.pure @@ W.string ~attr:Attr.(fg lightcyan) @@ Name.Ctor.to_string name
      ; Lwd.pure @@ W.string "<"
      ; W.hbox @@ List.intersperse ~sep:(pad ~right:1 @@ Lwd.pure @@ W.string ",") @@ List.map args ~f:render_ty
      ; Lwd.pure @@ W.string ">"
      ]

and render_exists Ty.Exists.{ quants; body } =
  W.hbox
    [ pad ~right:1 @@ Lwd.pure @@ W.string ~attr:Attr.(st bold) "∃"
    ; W.hbox @@ List.intersperse ~sep:(pad ~right:1 @@ Lwd.pure @@ W.string ",") @@ List.map quants ~f:render_quant
    ; pad ~right:1 @@ Lwd.pure @@ W.string ~attr:Attr.(st bold) "."
    ; render_ty body
    ]

and render_quant quant = W.hbox [ Lwd.pure @@ W.string "("; render_ty_param quant; Lwd.pure @@ W.string ")" ]

and render_ty_param Ty.Param.{ name; param_bounds } =
  W.hbox
    [ pad ~right:1 @@ Lwd.pure @@ W.string ~attr:Attr.(fg green ++ st italic) @@ Name.Ty_param.to_string name.elem
    ; render_ty_param_bounds param_bounds
    ]

and render_ty_param_bounds Ty.Param_bounds.{ upper; lower } =
  W.hbox
    [ pad ~right:1 @@ Lwd.pure @@ W.string ~attr:Attr.(st italic) "as"
    ; pad ~right:1 @@ render_ty upper
    ; pad ~right:1 @@ Lwd.pure @@ W.string ~attr:Attr.(st italic) "super"
    ; render_ty lower
    ]
;;

let render_ty_refinement ty_rfmt =
  match ty_rfmt with
  | Ty.Refinement.Disjoint _ ->
    W.hbox
      [ pad ~right:1 @@ Lwd.pure @@ W.string "_"; Lwd.pure @@ W.string "←"; pad ~left:1 @@ Lwd.pure @@ W.string "⊥" ]
  | Ty.Refinement.Intersect_with (_, ty) ->
    W.hbox [ pad ~right:1 @@ Lwd.pure @@ W.string "_"; Lwd.pure @@ W.string "&"; pad ~left:1 @@ render_ty ty ]
  | Ty.Refinement.Replace_with ty ->
    W.hbox [ pad ~right:1 @@ Lwd.pure @@ W.string "_"; Lwd.pure @@ W.string "←"; pad ~left:1 @@ render_ty ty ]
;;

(* ~~ Program rendering ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)

let render_line gutter_width pred start_col end_col line_idx line =
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
        ; W.string ~attr:Attr.(fg lightwhite) (String.drop_prefix line end_col)
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
        ; W.string ~attr:Attr.(fg lightwhite) (String.drop_prefix line end_col)
        ]
      else [ W.string ~attr:Attr.(fg green) line ]
    else [ W.string ~attr:Attr.(fg @@ gray 10) line ]
  in
  let space_ui = Lwd.pure (Ui.space 2 0) in
  let gutter_ui =
    Lwd.pure
    @@ W.string
         ~attr:Attr.(st italic ++ fg black ++ bg lightyellow)
         ((String.pad_right ~len:gutter_width @@ Int.to_string line_num) ^ " │")
  in
  W.hbox (gutter_ui :: space_ui :: line_ui)
;;

let render_program lines span_opt =
  let gutter_width = String.length @@ Int.to_string @@ List.length lines in
  let pred =
    match span_opt with
    | None -> fun _ -> false, false, false
    | Some Span.{ start_; end_ } ->
      fun line_num -> line_num >= start_.line && line_num <= end_.line, line_num = start_.line, line_num = end_.line
  in
  let start_col, end_col =
    Option.value_map span_opt ~default:(0, 1) ~f:(fun Span.{ start_; end_ } ->
      let start_ = start_.offset - start_.bol
      and end_ = end_.offset - end_.bol in
      start_, end_)
  in
  W.vbox (List.mapi lines ~f:(render_line gutter_width pred start_col end_col))
;;

let nav =
  W.hbox
    [ Lwd.map2 st_oracle (Lwd.get st_step) ~f:(fun oracle step_opt ->
        Button.view ~label:"step into" ~on_click:(move_next ~oracle) ~enabled:(Option.is_some step_opt))
    ]
;;

(* ~~ State rendering ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)

let render_errors errs = W.vlist @@ List.map errs ~f:(fun err -> Lwd.pure @@ W.string @@ Typing.Err.to_string err)

let render_warnings warns =
  W.vlist @@ List.map warns ~f:(fun warn -> Lwd.pure @@ W.string @@ Typing.Warn.to_string warn)
;;

let render_span _span _lines = W.empty_lwd

let render_types span_tys =
  W.vlist
  @@ List.map span_tys ~f:(fun (span, ty) ->
    W.hbox
      [ Lwd.pure @@ W.string ~attr:Attr.(fg @@ gray 10) @@ Span.to_string span
      ; Lwd.pure @@ Ui.space 1 0
      ; Lwd.bind st_source ~f:(render_span span)
      ; Lwd.pure @@ Ui.space 1 0
      ; render_ty ty
      ])
;;

let render_state state_opt =
  match state_opt with
  | Some state ->
    Tabs.view
      [ ("types", fun _ -> render_types state.Typing.Eff.Debug.State.tys)
      ; ("errors", fun _ -> render_errors state.Typing.Eff.Debug.State.errs)
      ; ("warnings", fun _ -> render_warnings state.Typing.Eff.Debug.State.warns)
      ]
  | _ -> W.empty_lwd
;;

(* ~~ Context rendering ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)

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

let render_classish_ctxt ctxt = Lwd.pure @@ W.string @@ Ctxt.Classish_def.show ctxt
let render_fn_ctxt ctxt = Lwd.pure @@ W.string @@ Ctxt.Fn_def.show ctxt

let render_def_ctxt (ctxt_def : Ctxt.Def.t) =
  let Ctxt.Def.{ classish; fns } = ctxt_def in
  match classish, fns with
  | None, [] -> W.empty_lwd
  | None, fn_ctxt :: _ -> render_fn_ctxt fn_ctxt
  | Some classish, [] -> render_classish_ctxt classish
  | Some classish, fn_ctxt :: _ -> W.vbox [ render_classish_ctxt classish; render_fn_ctxt fn_ctxt ]
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
;;

let start file =
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
