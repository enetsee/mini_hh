open Reporting

type t =
  { status : Status.t
  ; state : State.t
  ; span : Span.t
  ; ctxt_def : Ctxt.Def.t
  ; ctxt_cont : Ctxt.Cont.t
  }
[@@deriving create, fields]

let next_typing status t ~oracle =
  let open Status.Typing_status in
  match status with
  | Asked_id { data; k } ->
    let ty_opt = Oracle.find_fn oracle data in
    { t with status = Effect.Deep.continue k ty_opt }
  | Got_fresh_tyvar { data; k } ->
    let ty, state = State.get_fresh_tyvar t.state ~prov:data in
    { t with status = Effect.Deep.continue k ty; state }
  | Logged_error { data; k } ->
    let state = State.add_error t.state data in
    { t with status = Effect.Deep.continue k (); state }
  | Logged_warning { data; k } ->
    let state = State.add_warning t.state data in
    { t with status = Effect.Deep.continue k (); state }
  | Logged_enter_synth_expr { data = { expr; ctxt_def; ctxt_cont }; k } ->
    let span = Located.span_of expr in
    { t with
      status = Effect.Deep.continue k (expr, ctxt_def, ctxt_cont)
    ; span
    ; ctxt_cont
    ; ctxt_def
    }
  | Logged_enter_check_expr { data = { expr; against; ctxt_def; ctxt_cont }; k }
    ->
    let span = Located.span_of expr in
    { t with
      status = Effect.Deep.continue k (expr, against, ctxt_def, ctxt_cont)
    ; span
    ; ctxt_cont
    }
  | Logged_exit_expr { data = { span; ty; expr_delta }; k } ->
    let state = State.add_ty_span t.state ty span in
    { t with status = Effect.Deep.continue k (ty, expr_delta); state; span }
  | Logged_enter_stmt { data = { stmt; ctxt_def; ctxt_cont }; k } ->
    let span = Located.span_of stmt in
    { t with
      status = Effect.Deep.continue k (stmt, ctxt_def, ctxt_cont)
    ; span
    ; ctxt_cont
    ; ctxt_def
    }
  | Logged_exit_stmt { data = { delta; span }; k } ->
    { t with status = Effect.Deep.continue k delta; span }
  | Logged_enter_classish_def
      { data = { classish_def; ctxt_def; ctxt_cont }; k } ->
    let span = Located.span_of classish_def in
    { t with
      status = Effect.Deep.continue k (classish_def, ctxt_def, ctxt_cont)
    ; span
    ; ctxt_def
    ; ctxt_cont
    }
  | Logged_exit_classish_def { k; data = span } ->
    { t with status = Effect.Deep.continue k (); span }
  | Logged_enter_fn_def { data = { fn_def; ctxt_def; ctxt_cont }; k } ->
    let span = Located.span_of fn_def in
    { t with
      status = Effect.Deep.continue k (fn_def, ctxt_def, ctxt_cont)
    ; span
    ; ctxt_cont
    ; ctxt_def
    }
  | Logged_exit_fn_def { k; data = span } ->
    { t with status = Effect.Deep.continue k (); span }
;;

let next_refinement status t ~oracle =
  let open Status.Refinement_status in
  match status with
  | Requested_fresh_ty_params { data; k } ->
    let state, data = State.fresh_ty_params t.state data in
    let status = Status.Refinement (Received_fresh_ty_params { data; k }) in
    { t with status; state }
  | Received_fresh_ty_params { data; k } ->
    let status = Effect.Deep.continue k data in
    { t with status }
  | Asked_up { data = { of_; at }; k } ->
    let data = Oracle.up oracle ~of_ ~at in
    let status = Status.Refinement (Answered_up { data; k }) in
    { t with status }
  | Answered_up { data; k } ->
    let status = Effect.Deep.continue k data in
    { t with status }
  | Asked_ty_param_variance { data; k } ->
    let data = Oracle.param_variances_opt oracle ~ctor:data in
    let status = Status.Refinement (Answered_ty_param_variance { data; k }) in
    { t with status }
  | Answered_ty_param_variance { data; k } ->
    let status = Effect.Deep.continue k data in
    { t with status }
  | Logged_exit { data = { ty_rfmt; ty_param_rfmt_opt; _ }; k } ->
    let status = Effect.Deep.continue k (ty_rfmt, ty_param_rfmt_opt) in
    { t with status }
  | Logged_enter_refinement { data = { ty_test; ty_scrut; ctxt_cont }; k } ->
    let status = Effect.Deep.continue k (ty_scrut, ty_test, ctxt_cont) in
    { t with status; ctxt_cont }
  | Logged_enter_ty { data = { ty_test; ty_scrut; ctxt_cont }; k } ->
    let status = Effect.Deep.continue k (ty_scrut, ty_test, ctxt_cont) in
    { t with status; ctxt_cont }
  | Logged_enter_existential_scrut
      { data = { ty_test; prov_scrut; ty_exists; ctxt_cont }; k } ->
    let status =
      Effect.Deep.continue k (prov_scrut, ty_exists, ty_test, ctxt_cont)
    in
    { t with status; ctxt_cont }
  | Logged_enter_existential_test
      { data = { ty_scrut; prov_test; ty_exists; ctxt_cont }; k } ->
    let status =
      Effect.Deep.continue k (ty_scrut, prov_test, ty_exists, ctxt_cont)
    in
    { t with status; ctxt_cont }
  | Logged_enter_union_scrut
      { data = { prov_scrut; tys_scrut; ty_test; ctxt_cont }; k } ->
    let status =
      Effect.Deep.continue k (prov_scrut, tys_scrut, ty_test, ctxt_cont)
    in
    { t with status; ctxt_cont }
  | Logged_enter_union_test
      { data = { ty_scrut; prov_test; tys_test; ctxt_cont }; k } ->
    let status =
      Effect.Deep.continue k (ty_scrut, prov_test, tys_test, ctxt_cont)
    in
    { t with status; ctxt_cont }
  | Logged_enter_inter_scrut
      { data = { prov_scrut; tys_scrut; ty_test; ctxt_cont }; k } ->
    let status =
      Effect.Deep.continue k (prov_scrut, tys_scrut, ty_test, ctxt_cont)
    in
    { t with status; ctxt_cont }
  | Logged_enter_inter_test
      { data = { ty_scrut; prov_test; tys_test; ctxt_cont }; k } ->
    let status =
      Effect.Deep.continue k (ty_scrut, prov_test, tys_test, ctxt_cont)
    in
    { t with status; ctxt_cont }
  | Logged_enter_top_level_generic_scrut
      { data = { ty_test; prov_scrut; name_scrut; ctxt_cont }; k } ->
    let status =
      Effect.Deep.continue k (prov_scrut, name_scrut, ty_test, ctxt_cont)
    in
    { t with status; ctxt_cont }
  | Logged_enter_top_level_generic_test
      { data = { ty_scrut; prov_test; name_test; ctxt_cont }; k } ->
    let status =
      Effect.Deep.continue k (ty_scrut, prov_test, name_test, ctxt_cont)
    in
    { t with status; ctxt_cont }
  | Logged_enter_ctor
      { data = { prov_scrut; ctor_scrut; prov_test; ctor_test; ctxt_cont }; k }
    ->
    let status =
      Effect.Deep.continue
        k
        (prov_scrut, ctor_scrut, prov_test, ctor_test, ctxt_cont)
    in
    { t with status; ctxt_cont }
  | Logged_enter_ctor_arg
      { data = { ty_scrut; ty_test; variance; ctxt_cont }; k } ->
    let status =
      Effect.Deep.continue k (ty_scrut, ty_test, variance, ctxt_cont)
    in
    { t with status; ctxt_cont }
;;

let next_exposure status t ~oracle =
  let open Status.Exposure_status in
  match status with
  | Asked_up { data = { of_; at }; k } ->
    let data = Oracle.up oracle ~of_ ~at in
    let status = Status.Exposure (Answered_up { data; k }) in
    { t with status }
  | Answered_up { data; k } ->
    let status = Effect.Deep.continue k data in
    { t with status }
  | Asked_ctor { data; k } ->
    let data = Oracle.find_ctor oracle data in
    let status = Status.Exposure (Answered_ctor { data; k }) in
    { t with status }
  | Answered_ctor { data; k } ->
    let status = Effect.Deep.continue k data in
    { t with status }
  | Logged_enter_delta { data; k } ->
    let status = Effect.Deep.continue k data in
    { t with status }
  | Logged_exit_delta { data; k } ->
    let status = Effect.Deep.continue k data in
    { t with status }
  | Logged_enter_cont_delta { data; k } ->
    let status = Effect.Deep.continue k data in
    { t with status }
  | Logged_exit_cont_delta { data; k } ->
    let status = Effect.Deep.continue k data in
    { t with status }
  | Logged_exit_elem { data = { data; _ }; k } ->
    let status = Effect.Deep.continue k data in
    { t with status }
  | Logged_enter_ty { data = { elem = ty; ty_params; dir }; k } ->
    let status = Effect.Deep.continue k (ty, ty_params, dir) in
    { t with status }
  | Logged_enter_generic { data = { elem = prov, name; ty_params; dir }; k } ->
    let status = Effect.Deep.continue k (prov, name, ty_params, dir) in
    { t with status }
  | Logged_enter_union { data = { elem = prov, tys; ty_params; dir }; k } ->
    let status = Effect.Deep.continue k (prov, tys, ty_params, dir) in
    { t with status }
  | Logged_enter_inter { data = { elem = prov, tys; ty_params; dir }; k } ->
    let status = Effect.Deep.continue k (prov, tys, ty_params, dir) in
    { t with status }
  | Logged_enter_fn { data = { elem = prov, fn; ty_params; dir }; k } ->
    let status = Effect.Deep.continue k (prov, fn, ty_params, dir) in
    { t with status }
  | Logged_enter_tuple { data = { elem = prov, tuple; ty_params; dir }; k } ->
    let status = Effect.Deep.continue k (prov, tuple, ty_params, dir) in
    { t with status }
  | Logged_enter_ctor { data = { elem = prov, ctor; ty_params; dir }; k } ->
    let status = Effect.Deep.continue k (prov, ctor, ty_params, dir) in
    { t with status }
  | Logged_enter_exists { data = { elem = prov, exists; ty_params; dir }; k } ->
    let status = Effect.Deep.continue k (prov, exists, ty_params, dir) in
    { t with status }
;;

let next_subtyping status t ~oracle =
  let open Status.Subtyping_status in
  match status with
  | Observed_variance { data = { var; variance }; k } ->
    let state = State.observe_variance t.state ~var ~variance in
    let status = Effect.Deep.continue k () in
    { t with status; state }
  | Added_bound { data = { var; bound; upper_or_lower = Upper }; k } ->
    let state = State.add_upper_bound t.state ~var ~bound in
    let status = Effect.Deep.continue k () in
    { t with status; state }
  | Added_bound { data = { var; bound; upper_or_lower = Lower }; k } ->
    let state = State.add_lower_bound t.state ~var ~bound in
    let status = Effect.Deep.continue k () in
    { t with status; state }
  | Got_bounds { data = { var; upper_or_lower = Lower }; k } ->
    let data = State.get_lower_bounds t.state ~var in
    let status = Effect.Deep.continue k data in
    { t with status }
  | Got_bounds { data = { var; upper_or_lower = Upper }; k } ->
    let data = State.get_upper_bounds t.state ~var in
    let status = Effect.Deep.continue k data in
    { t with status }
  | Got_fresh_tyvar { data; k } ->
    let ty, state = State.get_fresh_tyvar t.state ~prov:data in
    { t with status = Effect.Deep.continue k ty; state }
  | Asked_up { data = { of_; at }; k } ->
    let data = Oracle.up oracle ~of_ ~at in
    let status = Status.Subtyping (Answered_up { data; k }) in
    { t with status }
  | Answered_up { data; k } ->
    let status = Effect.Deep.continue k data in
    { t with status }
  | Asked_ty_param_variances { data; k } ->
    let data = Oracle.param_variances_opt oracle ~ctor:data in
    let status = Status.Subtyping (Answered_ty_param_variances { data; k }) in
    { t with status }
  | Answered_ty_param_variances { data; k } ->
    let status = Effect.Deep.continue k data in
    { t with status }
  | Logged_enter_tell_prop { data = { prop; ctxt_cont }; k } ->
    let status = Effect.Deep.continue k (prop, ctxt_cont) in
    { t with status; ctxt_cont }
  | Logged_enter_tell_cstr { data = { cstr; ctxt_cont }; k } ->
    let status = Effect.Deep.continue k (cstr, ctxt_cont) in
    { t with status; ctxt_cont }
  | Logged_enter_tell_all { data = { props; errs; ctxt_cont }; k } ->
    let status = Effect.Deep.continue k (props, errs, ctxt_cont) in
    { t with status; ctxt_cont }
  | Logged_enter_tell_any { data = { props; errs; ctxt_cont }; k } ->
    let status = Effect.Deep.continue k (props, errs, ctxt_cont) in
    { t with status; ctxt_cont }
  | Logged_exit_tell { data = { err_opt; _ }; k } ->
    let status = Effect.Deep.continue k err_opt in
    { t with status }
;;

let next t ~oracle =
  let open Status in
  match t.status with
  | Completed | Failed _ -> None
  | Typing status -> Some (next_typing status t ~oracle)
  | Refinement status -> Some (next_refinement status t ~oracle)
  | Exposure status -> Some (next_exposure status t ~oracle)
  | Subtyping status -> Some (next_subtyping status t ~oracle)
;;

let event { status; _ } = Status.event status
let errors { state = { errs; _ }; _ } = errs
let warnings { state = { warns; _ }; _ } = warns
let tys { state = { tys; _ }; _ } = tys
