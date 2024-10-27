open Core
open Reporting

type _ Effect.t +=
  | Log_error : Err.t -> unit Effect.t
  | Log_warning : Warn.t -> unit Effect.t
  | Log_enter_expr : Span.t * Ctxt.Def.t * Ctxt.Cont.t -> (Ctxt.Def.t * Ctxt.Cont.t) Effect.t
  | Log_enter_stmt : Span.t * Ctxt.Def.t * Ctxt.Cont.t -> (Ctxt.Def.t * Ctxt.Cont.t) Effect.t
  | Log_enter_def : Span.t * Ctxt.Def.t * Ctxt.Cont.t -> (Ctxt.Def.t * Ctxt.Cont.t) Effect.t
  | Log_exit_expr : Span.t * Ty.t * Ctxt.Cont.Expr_delta.t -> (Ty.t * Ctxt.Cont.Expr_delta.t) Effect.t
  | Log_exit_stmt : Span.t * Ctxt.Delta.t -> Ctxt.Delta.t Effect.t
  | Log_exit_def : Span.t -> unit Effect.t
  | Tell_is_subtype :
      { ty_sub : Ty.t
      ; ty_super : Ty.t
      ; cont_ctxt : Ctxt.Cont.t
      }
      -> bool option Effect.t

let log_error err = Effect.perform (Log_error err)
let log_warning warn = Effect.perform (Log_warning warn)
let log_enter_expr span ctxt_def ctxt_cont = Effect.perform (Log_enter_expr (span, ctxt_def, ctxt_cont))
let log_enter_stmt span ctxt_def ctxt_cont = Effect.perform (Log_enter_stmt (span, ctxt_def, ctxt_cont))
let log_enter_def span ctxt_def ctxt_cont = Effect.perform (Log_enter_stmt (span, ctxt_def, ctxt_cont))
let log_exit_expr span (ty, expr_delta) = Effect.perform (Log_exit_expr (span, ty, expr_delta))
let log_exit_stmt span delta = Effect.perform (Log_exit_stmt (span, delta))
let log_exit_def span = Effect.perform (Log_exit_def span)
let tell_is_subtype ~ty_sub ~ty_super cont_ctxt = Effect.perform (Tell_is_subtype { ty_sub; ty_super; cont_ctxt })

let run_typing comp tys errs warns =
  let errs_ref = ref errs in
  let warns_ref = ref warns in
  let tys_ref = ref tys in
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
          | Log_enter_def (_span, ctxt_def, ctxt_cont) ->
            Some (fun (k : (a, _) Effect.Deep.continuation) -> Effect.Deep.continue k (ctxt_def, ctxt_cont))
          | Log_exit_expr (span, ty, expr_delta) ->
            tys_ref := (span, ty) :: !tys_ref;
            Some (fun (k : (a, _) Effect.Deep.continuation) -> Effect.Deep.continue k (ty, expr_delta))
          | Log_exit_stmt (_span, delta) ->
            Some (fun (k : (a, _) Effect.Deep.continuation) -> Effect.Deep.continue k delta)
          | Log_exit_def _span -> Some (fun (k : (a, _) Effect.Deep.continuation) -> Effect.Deep.continue k ())
          | Tell_is_subtype { ty_sub; ty_super; cont_ctxt } ->
            let err_opt = Subtyping.Tell.is_subtype ~ty_sub ~ty_super ~ctxt:cont_ctxt in
            let _ : unit = Option.iter err_opt ~f:(fun err -> errs_ref := Err.subtyping err :: !errs_ref) in
            let is_err = Option.is_some err_opt in
            Some (fun (k : (a, _) Effect.Deep.continuation) -> Effect.Deep.continue k (Some is_err))
          | _ -> None)
    ; retc = (fun _res -> !tys_ref, !errs_ref, !warns_ref)
    ; exnc = (fun exn -> raise exn)
    }
;;

let run comp oracle = run_typing (fun () -> Refinement.Eff.run comp 0 oracle) [] [] []
