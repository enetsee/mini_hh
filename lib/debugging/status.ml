open Reporting
open Common

module rec Status : sig
  type t =
    | Completed
    | Failed of exn
    | Typing of Typing_status.t
    | Refinement of Refinement_status.t
    | Exposure of Exposure_status.t
    | Subtyping of Subtyping_status.t
end =
  Status

and Suspension : sig
  type ('a, 'b) t =
    { data : 'a
    ; k : ('b, Status.t) Effect.Deep.continuation
    }
end =
  Suspension

and Typing_status : sig
  type t =
    | Logged_error of (Typing.Err.t, unit) Suspension.t
    | Logged_warning of (Typing.Warn.t, unit) Suspension.t
    | Logged_enter_synth_expr of
        ( Typing.Eff.enter_synth_expr
          , Lang.Expr.t * Ctxt.Def.t * Ctxt.Cont.t )
          Suspension.t
    | Logged_enter_check_expr of
        ( Typing.Eff.enter_check_expr
          , Lang.Expr.t * Ty.t * Ctxt.Def.t * Ctxt.Cont.t )
          Suspension.t
    | Logged_exit_expr of
        (Typing.Eff.exit_expr, Ty.t * Ctxt.Cont.Expr_delta.t) Suspension.t
    | Logged_enter_stmt of
        ( Typing.Eff.enter_stmt
          , Lang.Stmt.t * Ctxt.Def.t * Ctxt.Cont.t )
          Suspension.t
    | Logged_exit_stmt of (Typing.Eff.exit_stmt, Ctxt.Delta.t) Suspension.t
    | Logged_enter_classish_def of
        ( Typing.Eff.enter_classish_def
          , Lang.Classish_def.t Located.t * Ctxt.Def.t * Ctxt.Cont.t )
          Suspension.t
    | Logged_exit_classish_def of (Span.t, unit) Suspension.t
    | Logged_enter_fn_def of
        ( Typing.Eff.enter_fn_def
          , Lang.Fn_def.t Located.t * Ctxt.Def.t * Ctxt.Cont.t )
          Suspension.t
    | Logged_exit_fn_def of (Span.t, unit) Suspension.t
    | Got_fresh_tyvar of (Prov.t, Ty.t) Suspension.t
end =
  Typing_status

and Refinement_status : sig
  type t =
    | Requested_fresh_ty_params of (int, Name.Ty_param.t list) Suspension.t
    | Received_fresh_ty_params of
        (Name.Ty_param.t list, Name.Ty_param.t list) Suspension.t
    | Asked_up of
        (Refinement.Eff.ask_up, Oracle.Classish.instantiation) Suspension.t
    | Answered_up of
        ( Oracle.Classish.instantiation
          , Oracle.Classish.instantiation )
          Suspension.t
    | Asked_ty_param_variance of
        (Name.Ctor.t, Variance.t Located.t list option) Suspension.t
    | Answered_ty_param_variance of
        ( Variance.t Located.t list option
          , Variance.t Located.t list option )
          Suspension.t
    | Logged_exit of
        ( Refinement.Eff.exit
          , Ty.Refinement.t * (Prov.t * Ctxt.Ty_param.Refinement.t) option )
          Suspension.t
    | Logged_enter_refinement of
        (Refinement.Eff.enter_ty, Ty.t * Ty.t * Ctxt.Cont.t) Suspension.t
    | Logged_enter_ty of
        (Refinement.Eff.enter_ty, Ty.t * Ty.t * Ctxt.Cont.t) Suspension.t
    | Logged_enter_existential_scrut of
        ( Refinement.Eff.enter_existential_scrut
          , Prov.t * Ty.Exists.t * Ty.t * Ctxt.Cont.t )
          Suspension.t
    | Logged_enter_existential_test of
        ( Refinement.Eff.enter_existential_test
          , Ty.t * Prov.t * Ty.Exists.t * Ctxt.Cont.t )
          Suspension.t
    | Logged_enter_union_scrut of
        ( Refinement.Eff.enter_union_scrut
          , Prov.t * Ty.t list * Ty.t * Ctxt.Cont.t )
          Suspension.t
    | Logged_enter_union_test of
        ( Refinement.Eff.enter_union_test
          , Ty.t * Prov.t * Ty.t list * Ctxt.Cont.t )
          Suspension.t
    | Logged_enter_inter_scrut of
        ( Refinement.Eff.enter_inter_scrut
          , Prov.t * Ty.t list * Ty.t * Ctxt.Cont.t )
          Suspension.t
    | Logged_enter_inter_test of
        ( Refinement.Eff.enter_inter_test
          , Ty.t * Prov.t * Ty.t list * Ctxt.Cont.t )
          Suspension.t
    | Logged_enter_top_level_generic_scrut of
        ( Refinement.Eff.enter_top_level_generic_scrut
          , Prov.t * Name.Ty_param.t * Ty.t * Ctxt.Cont.t )
          Suspension.t
    | Logged_enter_top_level_generic_test of
        ( Refinement.Eff.enter_top_level_generic_test
          , Ty.t * Prov.t * Name.Ty_param.t * Ctxt.Cont.t )
          Suspension.t
    | Logged_enter_ctor of
        ( Refinement.Eff.enter_ctor
          , Prov.t * Ty.Ctor.t * Prov.t * Ty.Ctor.t * Ctxt.Cont.t )
          Suspension.t
    | Logged_enter_ctor_arg of
        ( Refinement.Eff.enter_ctor_arg
          , Ty.t * Ty.t * Variance.t Located.t * Ctxt.Cont.t )
          Suspension.t
end =
  Refinement_status

and Exposure_status : sig
  type t =
    | Asked_up of
        (Exposure.Eff.ask_up, Oracle.Classish.instantiation) Suspension.t
    | Answered_up of
        ( Oracle.Classish.instantiation
          , Oracle.Classish.instantiation )
          Suspension.t
    | Asked_ctor of
        ( Name.Ctor.t
          , (Lang.Ty_param_def.t list * Ty.t list Name.Ctor.Map.t) option )
          Suspension.t
    | Answered_ctor of
        ( (Lang.Ty_param_def.t list * Ty.t list Name.Ctor.Map.t) option
          , (Lang.Ty_param_def.t list * Ty.t list Name.Ctor.Map.t) option )
          Suspension.t
    | Logged_enter_delta of (Ctxt.Delta.t, Ctxt.Delta.t) Suspension.t
    | Logged_exit_delta of (Ctxt.Delta.t, Ctxt.Delta.t) Suspension.t
    | Logged_enter_cont_delta of
        (Ctxt.Cont.Delta.t, Ctxt.Cont.Delta.t) Suspension.t
    | Logged_exit_cont_delta of
        (Ctxt.Cont.Delta.t, Ctxt.Cont.Delta.t) Suspension.t
    | Logged_exit_elem of
        (Exposure.Eff.exit, (Ty.t, Exposure.Err.Set.t) result) Suspension.t
    | Logged_enter_ty of
        ( Ty.t Exposure.Eff.enter
          , Ty.t * Ctxt.Ty_param.t * Exposure.Dir.t )
          Suspension.t
    | Logged_enter_generic of
        ( (Prov.t * Name.Ty_param.t) Exposure.Eff.enter
          , Prov.t * Name.Ty_param.t * Ctxt.Ty_param.t * Exposure.Dir.t )
          Suspension.t
    | Logged_enter_union of
        ( (Prov.t * Ty.t list) Exposure.Eff.enter
          , Prov.t * Ty.t list * Ctxt.Ty_param.t * Exposure.Dir.t )
          Suspension.t
    | Logged_enter_inter of
        ( (Prov.t * Ty.t list) Exposure.Eff.enter
          , Prov.t * Ty.t list * Ctxt.Ty_param.t * Exposure.Dir.t )
          Suspension.t
    | Logged_enter_fn of
        ( (Prov.t * Ty.Fn.t) Exposure.Eff.enter
          , Prov.t * Ty.Fn.t * Ctxt.Ty_param.t * Exposure.Dir.t )
          Suspension.t
    | Logged_enter_tuple of
        ( (Prov.t * Ty.Tuple.t) Exposure.Eff.enter
          , Prov.t * Ty.Tuple.t * Ctxt.Ty_param.t * Exposure.Dir.t )
          Suspension.t
    | Logged_enter_ctor of
        ( (Prov.t * Ty.Ctor.t) Exposure.Eff.enter
          , Prov.t * Ty.Ctor.t * Ctxt.Ty_param.t * Exposure.Dir.t )
          Suspension.t
    | Logged_enter_exists of
        ( (Prov.t * Ty.Exists.t) Exposure.Eff.enter
          , Prov.t * Ty.Exists.t * Ctxt.Ty_param.t * Exposure.Dir.t )
          Suspension.t
end =
  Exposure_status

and Subtyping_status : sig
  type t =
    | Asked_up of
        (Subtyping.Eff.ask_up, Oracle.Classish.instantiation) Suspension.t
    | Answered_up of
        ( Oracle.Classish.instantiation
          , Oracle.Classish.instantiation )
          Suspension.t
    | Asked_ty_param_variances of
        (Name.Ctor.t, Variance.t Located.t list option) Suspension.t
    | Answered_ty_param_variances of
        ( Variance.t Located.t list option
          , Variance.t Located.t list option )
          Suspension.t
    | Logged_enter_tell_prop of
        ( Subtyping.Eff.enter_tell_prop
          , Subtyping.Prop.t * Ctxt.Cont.t )
          Suspension.t
    | Logged_enter_tell_cstr of
        ( Subtyping.Eff.enter_tell_cstr
          , Subtyping.Cstr.t * Ctxt.Cont.t )
          Suspension.t
    | Logged_enter_tell_all of
        ( Subtyping.Eff.enter_tell_all
          , Subtyping.Prop.t list * Subtyping.Err.t list * Ctxt.Cont.t )
          Suspension.t
    | Logged_enter_tell_any of
        ( Subtyping.Eff.enter_tell_any
          , Subtyping.Prop.t list * Subtyping.Err.t list * Ctxt.Cont.t )
          Suspension.t
    | Logged_exit_tell of
        (Subtyping.Eff.exit_tell, Subtyping.Err.t option) Suspension.t
    | Added_bound of (Subtyping.Eff.add_bound, unit) Suspension.t
    | Got_bounds of (Subtyping.Eff.get_bounds, Ty.t list) Suspension.t
end =
  Subtyping_status

include Status

module Event = struct
  type alert =
    | Error
    | Warning

  type query =
    | Up
    | Ctor
    | Variance

  type exposure_elem =
    | Delta
    | Cont_delta
    | Ty
    | Union
    | Inter
    | Generic
    | Ctor
    | Exists
    | Fn
    | Tuple

  type typing_elem =
    | Expr of Span.t
    | Stmt of Span.t
    | Classish_def of Span.t
    | Fn_def of Span.t

  type subtyping_elem =
    | Prop
    | Cstr
    | All
    | Any

  type side =
    | Scrut
    | Test

  type refinement_elem =
    | Refinement
    | Ty
    | Exists of side
    | Union of side
    | Inter of side
    | Top_level_generic of side
    | Ctor
    | Ctor_arg

  type elem =
    | Typing_elem of typing_elem
    | Subtyping_elem of subtyping_elem
    | Refinement_elem of refinement_elem
    | Exposure_elem of exposure_elem

  type subtyping_state =
    | Lower_bounds
    | Upper_bounds
    | Tyvar

  type state = Subtyping_state of subtyping_state

  type comp =
    | Typing
    | Subtyping
    | Refinement
    | Exposure

  type asset =
    | Ty_param
    | Ty_var

  type t =
    | Fail
    | Complete
    | Raise of comp * alert
    | Ask of comp * query
    | Answer of comp * query
    | Requested of comp * asset
    | Received of comp * asset
    | Enter of comp * elem
    | Exit of comp * elem
    | Put of comp * state
    | Got of comp * state

  let typing_event status =
    let open Typing_status in
    match status with
    | Logged_error _ -> Raise (Typing, Error)
    | Logged_warning _ -> Raise (Typing, Warning)
    | Logged_enter_synth_expr { data = { expr = Located.{ span; _ }; _ }; _ } ->
      Enter (Typing, Typing_elem (Expr span))
    | Logged_enter_check_expr { data = { expr = Located.{ span; _ }; _ }; _ } ->
      Enter (Typing, Typing_elem (Expr span))
    | Logged_exit_expr { data = { span; _ }; _ } ->
      Exit (Typing, Typing_elem (Expr span))
    | Logged_enter_stmt { data = { stmt = Located.{ span; _ }; _ }; _ } ->
      Enter (Typing, Typing_elem (Stmt span))
    | Logged_exit_stmt { data = { span; _ }; _ } ->
      Exit (Typing, Typing_elem (Expr span))
    | Logged_enter_fn_def { data = { fn_def = Located.{ span; _ }; _ }; _ } ->
      Enter (Typing, Typing_elem (Fn_def span))
    | Logged_enter_classish_def
        { data = { classish_def = Located.{ span; _ }; _ }; _ } ->
      Enter (Typing, Typing_elem (Classish_def span))
    | Logged_exit_classish_def { data = span; _ } ->
      Exit (Typing, Typing_elem (Classish_def span))
    | Logged_exit_fn_def { data = span; _ } ->
      Exit (Typing, Typing_elem (Fn_def span))
    | Got_fresh_tyvar _ -> Got (Typing, Subtyping_state Tyvar)
  ;;

  let subtyping_event status =
    let open Subtyping_status in
    match status with
    | Asked_up _ -> Ask (Subtyping, Up)
    | Answered_up _ -> Answer (Subtyping, Up)
    | Asked_ty_param_variances _ -> Ask (Subtyping, Variance)
    | Answered_ty_param_variances _ -> Answer (Subtyping, Variance)
    | Logged_enter_tell_prop _ -> Enter (Subtyping, Subtyping_elem Prop)
    | Logged_exit_tell { data = { tell = Subtyping.Eff.Prop; _ }; _ } ->
      Exit (Subtyping, Subtyping_elem Prop)
    | Logged_enter_tell_cstr _ -> Enter (Subtyping, Subtyping_elem Cstr)
    | Logged_exit_tell { data = { tell = Subtyping.Eff.Cstr; _ }; _ } ->
      Exit (Subtyping, Subtyping_elem Cstr)
    | Logged_enter_tell_all _ -> Enter (Subtyping, Subtyping_elem All)
    | Logged_exit_tell { data = { tell = Subtyping.Eff.All; _ }; _ } ->
      Exit (Subtyping, Subtyping_elem All)
    | Logged_enter_tell_any _ -> Enter (Subtyping, Subtyping_elem Any)
    | Logged_exit_tell { data = { tell = Subtyping.Eff.Any; _ }; _ } ->
      Exit (Subtyping, Subtyping_elem Any)
    | Added_bound { data = { upper_or_lower = Upper; _ }; _ } ->
      Put (Subtyping, Subtyping_state Upper_bounds)
    | Added_bound { data = { upper_or_lower = Lower; _ }; _ } ->
      Put (Subtyping, Subtyping_state Lower_bounds)
    | Got_bounds { data = { upper_or_lower = Upper; _ }; _ } ->
      Got (Subtyping, Subtyping_state Upper_bounds)
    | Got_bounds { data = { upper_or_lower = Lower; _ }; _ } ->
      Got (Subtyping, Subtyping_state Lower_bounds)
  ;;

  let exposure_event status =
    let open Exposure_status in
    match status with
    | Asked_up _ -> Ask (Exposure, Up)
    | Answered_up _ -> Answer (Exposure, Up)
    | Asked_ctor _ -> Ask (Exposure, Ctor)
    | Answered_ctor _ -> Answer (Exposure, Ctor)
    | Logged_enter_delta _ -> Enter (Exposure, Exposure_elem Delta)
    | Logged_exit_delta _ -> Exit (Exposure, Exposure_elem Delta)
    | Logged_enter_cont_delta _ -> Enter (Exposure, Exposure_elem Cont_delta)
    | Logged_exit_cont_delta _ -> Exit (Exposure, Exposure_elem Cont_delta)
    | Logged_enter_ty _ -> Enter (Exposure, Exposure_elem Ty)
    | Logged_exit_elem { data = { elem = Ty; _ }; _ } ->
      Exit (Exposure, Exposure_elem Ty)
    | Logged_enter_generic _ -> Enter (Exposure, Exposure_elem Generic)
    | Logged_exit_elem { data = { elem = Generic; _ }; _ } ->
      Exit (Exposure, Exposure_elem Generic)
    | Logged_enter_union _ -> Enter (Exposure, Exposure_elem Union)
    | Logged_exit_elem { data = { elem = Union; _ }; _ } ->
      Exit (Exposure, Exposure_elem Union)
    | Logged_enter_inter _ -> Enter (Exposure, Exposure_elem Inter)
    | Logged_exit_elem { data = { elem = Inter; _ }; _ } ->
      Exit (Exposure, Exposure_elem Inter)
    | Logged_enter_fn _ -> Enter (Exposure, Exposure_elem Fn)
    | Logged_exit_elem { data = { elem = Fn; _ }; _ } ->
      Exit (Exposure, Exposure_elem Fn)
    | Logged_enter_tuple _ -> Enter (Exposure, Exposure_elem Tuple)
    | Logged_exit_elem { data = { elem = Tuple; _ }; _ } ->
      Exit (Exposure, Exposure_elem Tuple)
    | Logged_enter_ctor _ -> Enter (Exposure, Exposure_elem Ctor)
    | Logged_exit_elem { data = { elem = Ctor; _ }; _ } ->
      Exit (Exposure, Exposure_elem Ctor)
    | Logged_enter_exists _ -> Enter (Exposure, Exposure_elem Exists)
    | Logged_exit_elem { data = { elem = Exists; _ }; _ } ->
      Exit (Exposure, Exposure_elem Exists)
  ;;

  let refinement_event status =
    let open Refinement_status in
    match status with
    | Requested_fresh_ty_params _ -> Requested (Refinement, Ty_param)
    | Received_fresh_ty_params _ -> Received (Refinement, Ty_param)
    | Asked_up _ -> Ask (Refinement, Up)
    | Answered_up _ -> Answer (Refinement, Up)
    | Asked_ty_param_variance _ -> Ask (Refinement, Variance)
    | Answered_ty_param_variance _ -> Answer (Refinement, Variance)
    | Logged_enter_refinement _ -> Enter (Refinement, Refinement_elem Refinement)
    | Logged_exit { data = { elem = Refinement; _ }; _ } ->
      Exit (Refinement, Refinement_elem Refinement)
    | Logged_enter_ty _ -> Enter (Refinement, Refinement_elem Ty)
    | Logged_exit { data = { elem = Ty; _ }; _ } ->
      Exit (Refinement, Refinement_elem Ty)
    | Logged_enter_existential_scrut _ ->
      Enter (Refinement, Refinement_elem (Exists Scrut))
    | Logged_exit { data = { elem = Exists Scrut; _ }; _ } ->
      Exit (Refinement, Refinement_elem (Exists Scrut))
    | Logged_enter_existential_test _ ->
      Enter (Refinement, Refinement_elem (Exists Test))
    | Logged_exit { data = { elem = Exists Test; _ }; _ } ->
      Exit (Refinement, Refinement_elem (Exists Test))
    | Logged_enter_union_scrut _ ->
      Enter (Refinement, Refinement_elem (Union Scrut))
    | Logged_exit { data = { elem = Union Scrut; _ }; _ } ->
      Exit (Refinement, Refinement_elem (Union Scrut))
    | Logged_enter_union_test _ ->
      Enter (Refinement, Refinement_elem (Union Test))
    | Logged_exit { data = { elem = Union Test; _ }; _ } ->
      Exit (Refinement, Refinement_elem (Union Test))
    | Logged_enter_inter_scrut _ ->
      Enter (Refinement, Refinement_elem (Inter Scrut))
    | Logged_exit { data = { elem = Inter Scrut; _ }; _ } ->
      Exit (Refinement, Refinement_elem (Inter Scrut))
    | Logged_enter_inter_test _ ->
      Enter (Refinement, Refinement_elem (Inter Test))
    | Logged_exit { data = { elem = Inter Test; _ }; _ } ->
      Exit (Refinement, Refinement_elem (Inter Test))
    | Logged_enter_top_level_generic_scrut _ ->
      Enter (Refinement, Refinement_elem (Top_level_generic Scrut))
    | Logged_exit { data = { elem = Top_level_generic Scrut; _ }; _ } ->
      Exit (Refinement, Refinement_elem (Top_level_generic Scrut))
    | Logged_enter_top_level_generic_test _ ->
      Enter (Refinement, Refinement_elem (Top_level_generic Test))
    | Logged_exit { data = { elem = Top_level_generic Test; _ }; _ } ->
      Exit (Refinement, Refinement_elem (Top_level_generic Test))
    | Logged_enter_ctor _ -> Enter (Refinement, Refinement_elem Ctor)
    | Logged_exit { data = { elem = Ctor; _ }; _ } ->
      Exit (Refinement, Refinement_elem Ctor)
    | Logged_enter_ctor_arg _ -> Enter (Refinement, Refinement_elem Ctor_arg)
    | Logged_exit { data = { elem = Ctor_arg; _ }; _ } ->
      Exit (Refinement, Refinement_elem Ctor_arg)
  ;;

  let span_opt = function
    | Enter (_, Typing_elem (Expr span))
    | Enter (_, Typing_elem (Stmt span))
    | Enter (_, Typing_elem (Fn_def span))
    | Enter (_, Typing_elem (Classish_def span))
    | Exit (_, Typing_elem (Expr span))
    | Exit (_, Typing_elem (Stmt span))
    | Exit (_, Typing_elem (Fn_def span))
    | Exit (_, Typing_elem (Classish_def span)) -> Some span
    | Fail
    | Complete
    | Enter _
    | Exit _
    | Raise _
    | Ask _
    | Answer _
    | Requested _
    | Received _
    | Got _
    | Put _ -> None
  ;;
end

let event t =
  match t with
  | Completed -> Event.Complete
  | Failed _ -> Event.Fail
  | Typing status -> Event.typing_event status
  | Subtyping status -> Event.subtyping_event status
  | Exposure status -> Event.exposure_event status
  | Refinement status -> Event.refinement_event status
;;
