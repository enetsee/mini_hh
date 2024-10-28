open Core
open Common
open Reporting

type _ Effect.t +=
  | Log_error : Err.t -> unit Effect.t
  | Log_warning : Warn.t -> unit Effect.t
  | Log_enter_expr : Span.t * Ctxt.Def.t * Ctxt.Cont.t -> (Ctxt.Def.t * Ctxt.Cont.t) Effect.t
  | Log_exit_expr : Span.t * Ty.t * Ctxt.Cont.Expr_delta.t -> (Ty.t * Ctxt.Cont.Expr_delta.t) Effect.t
  | Log_enter_stmt : Span.t * Ctxt.Def.t * Ctxt.Cont.t -> (Ctxt.Def.t * Ctxt.Cont.t) Effect.t
  | Log_exit_stmt : Span.t * Ctxt.Delta.t -> Ctxt.Delta.t Effect.t
  | Log_enter_classish_def : Span.t * Name.Ctor.t * Ctxt.Def.t * Ctxt.Cont.t -> (Ctxt.Def.t * Ctxt.Cont.t) Effect.t
  | Log_exit_classish_def : Span.t -> unit Effect.t
  | Log_enter_fn_def : Span.t * Name.Fn.t * Ctxt.Def.t * Ctxt.Cont.t -> (Ctxt.Def.t * Ctxt.Cont.t) Effect.t
  | Log_exit_fn_def : Span.t -> unit Effect.t

let log_error err = Effect.perform (Log_error err)
let log_warning warn = Effect.perform (Log_warning warn)
let log_enter_expr span ctxt_def ctxt_cont = Effect.perform (Log_enter_expr (span, ctxt_def, ctxt_cont))
let log_exit_expr span (ty, expr_delta) = Effect.perform (Log_exit_expr (span, ty, expr_delta))
let log_enter_stmt span ctxt_def ctxt_cont = Effect.perform (Log_enter_stmt (span, ctxt_def, ctxt_cont))
let log_exit_stmt span delta = Effect.perform (Log_exit_stmt (span, delta))

let log_enter_classish_def span name ctxt_def ctxt_cont =
  Effect.perform (Log_enter_classish_def (span, name, ctxt_def, ctxt_cont))
;;

let log_exit_classish_def span = Effect.perform (Log_exit_classish_def span)
let log_enter_fn_def span name ctxt_def ctxt_cont = Effect.perform (Log_enter_fn_def (span, name, ctxt_def, ctxt_cont))
let log_exit_fn_def span = Effect.perform (Log_exit_fn_def span)

let run_typing comp (tys_ref, errs_ref, warns_ref) =
  Effect.Deep.match_with
    comp
    ()
    { effc =
        (fun (type a) (eff : a Effect.t) ->
          match eff with
          | Log_error err ->
            errs_ref := err :: !errs_ref;
            Some (fun (k : (a, _) Effect.Deep.continuation) -> Effect.Deep.continue k ())
          | Log_warning warn ->
            warns_ref := warn :: !warns_ref;
            Some (fun (k : (a, _) Effect.Deep.continuation) -> Effect.Deep.continue k ())
          | Log_enter_expr (_span, ctxt_def, ctxt_cont) ->
            Some (fun (k : (a, _) Effect.Deep.continuation) -> Effect.Deep.continue k (ctxt_def, ctxt_cont))
          | Log_enter_stmt (_span, ctxt_def, ctxt_cont) ->
            Some (fun (k : (a, _) Effect.Deep.continuation) -> Effect.Deep.continue k (ctxt_def, ctxt_cont))
          | Log_enter_classish_def (_span, _name, ctxt_def, ctxt_cont) ->
            Some (fun (k : (a, _) Effect.Deep.continuation) -> Effect.Deep.continue k (ctxt_def, ctxt_cont))
          | Log_enter_fn_def (_span, _name, ctxt_def, ctxt_cont) ->
            Some (fun (k : (a, _) Effect.Deep.continuation) -> Effect.Deep.continue k (ctxt_def, ctxt_cont))
          | Log_exit_expr (span, ty, expr_delta) ->
            tys_ref := (span, ty) :: !tys_ref;
            Some (fun (k : (a, _) Effect.Deep.continuation) -> Effect.Deep.continue k (ty, expr_delta))
          | Log_exit_stmt (_span, delta) ->
            Some (fun (k : (a, _) Effect.Deep.continuation) -> Effect.Deep.continue k delta)
          | Log_exit_classish_def _span -> Some (fun (k : (a, _) Effect.Deep.continuation) -> Effect.Deep.continue k ())
          | Log_exit_fn_def _span -> Some (fun (k : (a, _) Effect.Deep.continuation) -> Effect.Deep.continue k ())
          | _ -> None)
    ; retc = (fun _res -> ())
    ; exnc = (fun exn -> raise exn)
    }
;;

let run comp oracle =
  let tys = ref []
  and errs = ref []
  and warns = ref [] in
  let _ : unit = run_typing (fun () -> Refinement.Eff.run comp 0 oracle) (tys, errs, warns) in
  !tys, !errs, !warns
;;

(* ~~ Debugging handler ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)

type status =
  | Entered_expr of
      { span : Span.t
      ; ctxt_def : Ctxt.Def.t
      ; ctxt_cont : Ctxt.Cont.t
      ; k : (Ctxt.Def.t * Ctxt.Cont.t, status) Effect.Deep.continuation
      }
  | Exited_expr of
      { span : Span.t
      ; ty : Ty.t
      ; expr_delta : Ctxt.Cont.Expr_delta.t
      ; k : (Ty.t * Ctxt.Cont.Expr_delta.t, status) Effect.Deep.continuation
      }
  | Entered_stmt of
      { span : Span.t
      ; ctxt_def : Ctxt.Def.t
      ; ctxt_cont : Ctxt.Cont.t
      ; k : (Ctxt.Def.t * Ctxt.Cont.t, status) Effect.Deep.continuation
      }
  | Exited_stmt of
      { span : Span.t
      ; delta : Ctxt.Delta.t
      ; k : (Ctxt.Delta.t, status) Effect.Deep.continuation
      }
  | Entered_classish_def of
      { span : Span.t
      ; name : Name.Ctor.t
      ; ctxt_def : Ctxt.Def.t
      ; ctxt_cont : Ctxt.Cont.t
      ; k : (Ctxt.Def.t * Ctxt.Cont.t, status) Effect.Deep.continuation
      }
  | Exited_classish_def of
      { span : Span.t
      ; k : (unit, status) Effect.Deep.continuation
      }
  | Entered_fn_def of
      { span : Span.t
      ; name : Name.Fn.t
      ; ctxt_def : Ctxt.Def.t
      ; ctxt_cont : Ctxt.Cont.t
      ; k : (Ctxt.Def.t * Ctxt.Cont.t, status) Effect.Deep.continuation
      }
  | Exited_fn_def of
      { span : Span.t
      ; k : (unit, status) Effect.Deep.continuation
      }
  | Raised_error of
      { err : Err.t
      ; k : (unit, status) Effect.Deep.continuation
      }
  | Raised_warning of
      { warn : Warn.t
      ; k : (unit, status) Effect.Deep.continuation
      }
  (* ~~ Refinement ~~ *)
  | Entered_refinement of
      { ty_test : Ty.t
      ; ty_scrut : Ty.t
      ; ctxt_cont : Ctxt.Cont.t
      ; k : (Ty.t * Ty.t * Ctxt.Cont.t, status) Effect.Deep.continuation
      }
  | Exited_refinement of
      { ty_rfmt : Ty.Refinement.t
      ; ty_param_rfmt_opt : (Prov.t * Ctxt.Ty_param.Refinement.t) option
      ; k : (Ty.Refinement.t * (Prov.t * Ctxt.Ty_param.Refinement.t) option, status) Effect.Deep.continuation
      }
  | Entered_refine_ty of
      { ty_test : Ty.t
      ; ty_scrut : Ty.t
      ; ctxt_cont : Ctxt.Cont.t
      ; k : (Ty.t * Ty.t * Ctxt.Cont.t, status) Effect.Deep.continuation
      }
  | Exited_refine_ty of
      { ty_rfmt : Ty.Refinement.t
      ; ty_param_rfmt_opt : (Prov.t * Ctxt.Ty_param.Refinement.t) option
      ; k : (Ty.Refinement.t * (Prov.t * Ctxt.Ty_param.Refinement.t) option, status) Effect.Deep.continuation
      }
  | Entered_refine_existential_scrut of
      { prov_scrut : Prov.t
      ; ty_exists : Ty.Exists.t
      ; ty_test : Ty.t
      ; ctxt_cont : Ctxt.Cont.t
      ; k : (Prov.t * Ty.Exists.t * Ty.t * Ctxt.Cont.t, status) Effect.Deep.continuation
      }
  | Exited_refine_existential_scrut of
      { ty_rfmt : Ty.Refinement.t
      ; ty_param_rfmt_opt : (Prov.t * Ctxt.Ty_param.Refinement.t) option
      ; k : (Ty.Refinement.t * (Prov.t * Ctxt.Ty_param.Refinement.t) option, status) Effect.Deep.continuation
      }
  | Entered_refine_existential_test of
      { ty_scrut : Ty.t
      ; prov_test : Prov.t
      ; ty_exists : Ty.Exists.t
      ; ctxt_cont : Ctxt.Cont.t
      ; k : (Ty.t * Prov.t * Ty.Exists.t * Ctxt.Cont.t, status) Effect.Deep.continuation
      }
  | Exited_refine_existential_test of
      { ty_rfmt : Ty.Refinement.t
      ; ty_param_rfmt_opt : (Prov.t * Ctxt.Ty_param.Refinement.t) option
      ; k : (Ty.Refinement.t * (Prov.t * Ctxt.Ty_param.Refinement.t) option, status) Effect.Deep.continuation
      }
  | Asked_up of
      { of_ : Ty.Ctor.t
      ; at : Name.Ctor.t
      ; k : (Ty.t list option, status) Effect.Deep.continuation
      }
  | Asked_ty_param_variances of
      { ctor : Name.Ctor.t
      ; k : (Variance.t Located.t list option, status) Effect.Deep.continuation
      }
  | Requested_fresh_ty_params of
      { n : int
      ; k : (Name.Ty_param.t list, status) Effect.Deep.continuation
      }
  | Complete
  | Failed of Exn.t

type state =
  { tys : (Span.t * Ty.t) list
  ; errs : Err.t list
  ; warns : Warn.t list
  ; ty_param_name_source : int
  }

let next status ~oracle ~state =
  match status with
  | Asked_up { of_; at; k } ->
    let ty_args_opt = Oracle.up oracle ~of_ ~at in
    Effect.Deep.continue k ty_args_opt, state
  | Asked_ty_param_variances { ctor; k } ->
    let ty_param_vars_opt = Oracle.param_variances_opt oracle ~ctor in
    Effect.Deep.continue k ty_param_vars_opt, state
  | Requested_fresh_ty_params { n; k } ->
    let { ty_param_name_source; _ } = state in
    let offset = ty_param_name_source in
    let ty_param_name_source = offset + n in
    let names = List.init n ~f:(fun i -> Name.Ty_param.of_string @@ Format.sprintf {|T#%n|} (i + offset)) in
    let state = { state with ty_param_name_source } in
    Effect.Deep.continue k names, state
  | Complete -> Complete, state
  | Failed exn -> Failed exn, state
  | Raised_error { k; err } -> Effect.Deep.continue k (), { state with errs = err :: state.errs }
  | Raised_warning { k; warn } -> Effect.Deep.continue k (), { state with warns = warn :: state.warns }
  (* ~~ Logging effects for typing ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
  | Entered_expr { ctxt_def; ctxt_cont; k; _ } -> Effect.Deep.continue k (ctxt_def, ctxt_cont), state
  | Exited_expr { ty; expr_delta; k; _ } -> Effect.Deep.continue k (ty, expr_delta), state
  | Entered_stmt { ctxt_def; ctxt_cont; k; _ } -> Effect.Deep.continue k (ctxt_def, ctxt_cont), state
  | Exited_stmt { delta; k; _ } -> Effect.Deep.continue k delta, state
  | Entered_classish_def { ctxt_def; ctxt_cont; k; _ } -> Effect.Deep.continue k (ctxt_def, ctxt_cont), state
  | Exited_classish_def { k; _ } -> Effect.Deep.continue k (), state
  | Entered_fn_def { ctxt_def; ctxt_cont; k; _ } -> Effect.Deep.continue k (ctxt_def, ctxt_cont), state
  | Exited_fn_def { k; _ } -> Effect.Deep.continue k (), state
  | Entered_refinement { ty_test; ty_scrut; ctxt_cont; k } ->
    Effect.Deep.continue k (ty_test, ty_scrut, ctxt_cont), state
  (* ~~ Logging effects for refinement ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
  | Exited_refinement { ty_rfmt; ty_param_rfmt_opt; k } -> Effect.Deep.continue k (ty_rfmt, ty_param_rfmt_opt), state
  | Entered_refine_ty { ty_test; ty_scrut; ctxt_cont; k } ->
    Effect.Deep.continue k (ty_test, ty_scrut, ctxt_cont), state
  | Exited_refine_ty { ty_rfmt; ty_param_rfmt_opt; k } -> Effect.Deep.continue k (ty_rfmt, ty_param_rfmt_opt), state
  | Entered_refine_existential_scrut { prov_scrut; ty_exists; ty_test; ctxt_cont; k } ->
    Effect.Deep.continue k (prov_scrut, ty_exists, ty_test, ctxt_cont), state
  | Exited_refine_existential_scrut { ty_rfmt; ty_param_rfmt_opt; k } ->
    Effect.Deep.continue k (ty_rfmt, ty_param_rfmt_opt), state
  | Entered_refine_existential_test { ty_scrut; prov_test; ty_exists; ctxt_cont; k } ->
    Effect.Deep.continue k (ty_scrut, prov_test, ty_exists, ctxt_cont), state
  | Exited_refine_existential_test { ty_rfmt; ty_param_rfmt_opt; k } ->
    Effect.Deep.continue k (ty_rfmt, ty_param_rfmt_opt), state
;;

let step_typing comp =
  Effect.Deep.match_with
    comp
    ()
    { effc =
        (fun (type a) (eff : a Effect.t) ->
          match eff with
          | Log_error err -> Some (fun (k : (a, _) Effect.Deep.continuation) -> Raised_error { err; k })
          | Log_warning warn -> Some (fun (k : (a, _) Effect.Deep.continuation) -> Raised_warning { warn; k })
          | Log_enter_expr (span, ctxt_def, ctxt_cont) ->
            Some (fun (k : (a, _) Effect.Deep.continuation) -> Entered_expr { span; ctxt_def; ctxt_cont; k })
          | Log_enter_stmt (span, ctxt_def, ctxt_cont) ->
            Some (fun (k : (a, _) Effect.Deep.continuation) -> Entered_stmt { span; ctxt_def; ctxt_cont; k })
          | Log_enter_classish_def (span, name, ctxt_def, ctxt_cont) ->
            Some
              (fun (k : (a, _) Effect.Deep.continuation) -> Entered_classish_def { span; name; ctxt_def; ctxt_cont; k })
          | Log_enter_fn_def (span, name, ctxt_def, ctxt_cont) ->
            Some (fun (k : (a, _) Effect.Deep.continuation) -> Entered_fn_def { span; name; ctxt_def; ctxt_cont; k })
          | Log_exit_expr (span, ty, expr_delta) ->
            Some (fun (k : (a, _) Effect.Deep.continuation) -> Exited_expr { span; ty; expr_delta; k })
          | Log_exit_stmt (span, delta) ->
            Some (fun (k : (a, _) Effect.Deep.continuation) -> Exited_stmt { span; delta; k })
          | Log_exit_classish_def span ->
            Some (fun (k : (a, _) Effect.Deep.continuation) -> Exited_classish_def { span; k })
          | Log_exit_fn_def span -> Some (fun (k : (a, _) Effect.Deep.continuation) -> Exited_classish_def { span; k })
          (* ~~ Refinement ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
          | Refinement.Eff.Log_enter_refinement { ty_test; ty_scrut; ctxt_cont } ->
            Some (fun (k : (a, _) Effect.Deep.continuation) -> Entered_refinement { ty_test; ty_scrut; ctxt_cont; k })
          | Refinement.Eff.Log_exit_refinement { ty_rfmt; ty_param_rfmt_opt } ->
            Some (fun (k : (a, _) Effect.Deep.continuation) -> Exited_refinement { ty_rfmt; ty_param_rfmt_opt; k })
          | Refinement.Eff.Log_enter_refine_ty { ty_test; ty_scrut; ctxt_cont } ->
            Some (fun (k : (a, _) Effect.Deep.continuation) -> Entered_refine_ty { ty_test; ty_scrut; ctxt_cont; k })
          | Refinement.Eff.Log_exit_refine_ty { ty_rfmt; ty_param_rfmt_opt } ->
            Some (fun (k : (a, _) Effect.Deep.continuation) -> Exited_refine_ty { ty_rfmt; ty_param_rfmt_opt; k })
          | Refinement.Eff.Log_enter_refine_existential_scrut { prov_scrut; ty_exists; ty_test; ctxt_cont } ->
            Some
              (fun (k : (a, _) Effect.Deep.continuation) ->
                Entered_refine_existential_scrut { prov_scrut; ty_exists; ty_test; ctxt_cont; k })
          | Refinement.Eff.Log_exit_refine_existential_scrut { ty_rfmt; ty_param_rfmt_opt } ->
            Some
              (fun (k : (a, _) Effect.Deep.continuation) ->
                Exited_refine_existential_scrut { ty_rfmt; ty_param_rfmt_opt; k })
          | Refinement.Eff.Log_enter_refine_existential_test { ty_scrut; prov_test; ty_exists; ctxt_cont } ->
            Some
              (fun (k : (a, _) Effect.Deep.continuation) ->
                Entered_refine_existential_test { ty_scrut; prov_test; ty_exists; ctxt_cont; k })
          | Refinement.Eff.Log_exit_refine_existential_test { ty_rfmt; ty_param_rfmt_opt } ->
            Some
              (fun (k : (a, _) Effect.Deep.continuation) ->
                Exited_refine_existential_test { ty_rfmt; ty_param_rfmt_opt; k })
          (* ~~ Refinement other ~~ *)
          | Refinement.Eff.Gen_fresh_ty_params n ->
            Some (fun (k : (a, _) Effect.Deep.continuation) -> Requested_fresh_ty_params { n; k })
          | Refinement.Eff.Ask_up { of_; at } ->
            Some (fun (k : (a, _) Effect.Deep.continuation) -> Asked_up { of_; at; k })
          | Refinement.Eff.Ask_ty_param_variances ctor ->
            Some (fun (k : (a, _) Effect.Deep.continuation) -> Asked_ty_param_variances { ctor; k })
          | _ -> None)
    ; retc = (fun _res -> Complete)
    ; exnc = (fun exn -> Failed exn)
    }
;;

let debug comp = step_typing comp
