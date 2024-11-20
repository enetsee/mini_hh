open Core
open Reporting

type enter_synth_expr =
  { expr : Lang.Expr.t
  ; ctxt_def : Ctxt.Def.t
  ; ctxt_cont : Ctxt.Cont.t
  }

type enter_check_expr =
  { expr : Lang.Expr.t
  ; against : Ty.t
  ; ctxt_def : Ctxt.Def.t
  ; ctxt_cont : Ctxt.Cont.t
  }

type exit_expr =
  { span : Span.t
  ; ty : Ty.t
  ; expr_delta : Ctxt.Cont.Expr_delta.t
  }

type enter_stmt =
  { stmt : Lang.Stmt.t
  ; ctxt_def : Ctxt.Def.t
  ; ctxt_cont : Ctxt.Cont.t
  }

type exit_stmt =
  { span : Span.t
  ; delta : Ctxt.Delta.t
  }

type enter_classish_def =
  { classish_def : Lang.Classish_def.t Located.t
  ; ctxt_def : Ctxt.Def.t
  ; ctxt_cont : Ctxt.Cont.t
  }

type enter_fn_def =
  { fn_def : Lang.Fn_def.t Located.t
  ; ctxt_def : Ctxt.Def.t
  ; ctxt_cont : Ctxt.Cont.t
  }

type _ Effect.t +=
  | Log_error : Err.t -> unit Effect.t
  | Log_warning : Warn.t -> unit Effect.t
  | Log_enter_synth_expr :
      enter_synth_expr
      -> (Lang.Expr.t * Ctxt.Def.t * Ctxt.Cont.t) Effect.t
  | Log_enter_check_expr :
      enter_check_expr
      -> (Lang.Expr.t * Ty.t * Ctxt.Def.t * Ctxt.Cont.t) Effect.t
  | Log_exit_expr : exit_expr -> (Ty.t * Ctxt.Cont.Expr_delta.t) Effect.t
  | Log_enter_stmt :
      enter_stmt
      -> (Lang.Stmt.t * Ctxt.Def.t * Ctxt.Cont.t) Effect.t
  | Log_exit_stmt : exit_stmt -> Ctxt.Delta.t Effect.t
  | Log_enter_classish_def :
      enter_classish_def
      -> (Lang.Classish_def.t Located.t * Ctxt.Def.t * Ctxt.Cont.t) Effect.t
  | Log_exit_classish_def : Span.t -> unit Effect.t
  | Log_enter_fn_def :
      enter_fn_def
      -> (Lang.Fn_def.t Located.t * Ctxt.Def.t * Ctxt.Cont.t) Effect.t
  | Log_exit_fn_def : Span.t -> unit Effect.t
  | Get_fresh_tyvar : Prov.t -> Ty.t Effect.t

let get_fresh_tyvar prov = Effect.perform (Get_fresh_tyvar prov)
let log_error err = Effect.perform (Log_error err)
let log_warning warn = Effect.perform (Log_warning warn)

let log_enter_synth_expr expr ctxt_def ctxt_cont =
  Effect.perform (Log_enter_synth_expr { expr; ctxt_def; ctxt_cont })
;;

let log_enter_check_expr expr against ctxt_def ctxt_cont =
  Effect.perform (Log_enter_check_expr { expr; against; ctxt_def; ctxt_cont })
;;

let log_exit_expr span (ty, expr_delta) =
  Effect.perform (Log_exit_expr { span; ty; expr_delta })
;;

let log_enter_stmt stmt ctxt_def ctxt_cont =
  Effect.perform (Log_enter_stmt { stmt; ctxt_def; ctxt_cont })
;;

let log_exit_stmt span delta = Effect.perform (Log_exit_stmt { span; delta })

let log_enter_classish_def classish_def ctxt_def ctxt_cont =
  Effect.perform (Log_enter_classish_def { classish_def; ctxt_def; ctxt_cont })
;;

let log_exit_classish_def span = Effect.perform (Log_exit_classish_def span)

let log_enter_fn_def fn_def ctxt_def ctxt_cont =
  Effect.perform (Log_enter_fn_def { fn_def; ctxt_def; ctxt_cont })
;;

let log_exit_fn_def span = Effect.perform (Log_exit_fn_def span)

let run_typing comp (tys_ref, errs_ref, warns_ref, st_ref) =
  Effect.Deep.match_with
    comp
    ()
    { effc =
        (fun (type a) (eff : a Effect.t) ->
          match eff with
          | Get_fresh_tyvar prov ->
            let ty, st = Subtyping.State.fresh_tyvar !st_ref ~prov in
            st_ref := st;
            Some
              (fun (k : (a, _) Effect.Deep.continuation) ->
                Effect.Deep.continue k ty)
          | Log_error err ->
            errs_ref := err :: !errs_ref;
            Some
              (fun (k : (a, _) Effect.Deep.continuation) ->
                Effect.Deep.continue k ())
          | Log_warning warn ->
            warns_ref := warn :: !warns_ref;
            Some
              (fun (k : (a, _) Effect.Deep.continuation) ->
                Effect.Deep.continue k ())
          | Log_enter_synth_expr { expr; ctxt_def; ctxt_cont } ->
            Some
              (fun (k : (a, _) Effect.Deep.continuation) ->
                Effect.Deep.continue k (expr, ctxt_def, ctxt_cont))
          | Log_enter_check_expr { expr; against; ctxt_def; ctxt_cont } ->
            Some
              (fun (k : (a, _) Effect.Deep.continuation) ->
                Effect.Deep.continue k (expr, against, ctxt_def, ctxt_cont))
          | Log_enter_stmt { stmt; ctxt_def; ctxt_cont } ->
            Some
              (fun (k : (a, _) Effect.Deep.continuation) ->
                Effect.Deep.continue k (stmt, ctxt_def, ctxt_cont))
          | Log_enter_classish_def { classish_def; ctxt_def; ctxt_cont } ->
            Some
              (fun (k : (a, _) Effect.Deep.continuation) ->
                Effect.Deep.continue k (classish_def, ctxt_def, ctxt_cont))
          | Log_enter_fn_def { fn_def; ctxt_def; ctxt_cont } ->
            Some
              (fun (k : (a, _) Effect.Deep.continuation) ->
                Effect.Deep.continue k (fn_def, ctxt_def, ctxt_cont))
          | Log_exit_expr { span; ty; expr_delta } ->
            tys_ref := (span, ty) :: !tys_ref;
            Some
              (fun (k : (a, _) Effect.Deep.continuation) ->
                Effect.Deep.continue k (ty, expr_delta))
          | Log_exit_stmt { delta; _ } ->
            Some
              (fun (k : (a, _) Effect.Deep.continuation) ->
                Effect.Deep.continue k delta)
          | Log_exit_classish_def _span ->
            Some
              (fun (k : (a, _) Effect.Deep.continuation) ->
                Effect.Deep.continue k ())
          | Log_exit_fn_def _span ->
            Some
              (fun (k : (a, _) Effect.Deep.continuation) ->
                Effect.Deep.continue k ())
          | _ -> None)
    ; retc = (fun _res -> ())
    ; exnc = (fun exn -> raise exn)
    }
;;

let run comp oracle =
  let tys = ref []
  and errs = ref []
  and warns = ref []
  and st_ref = ref Subtyping.State.empty in
  let _ : unit =
    run_typing
      (fun () ->
        let res, st =
          Subtyping.Eff.run
            (fun () ->
              Refinement.Eff.run
                (fun () -> Exposure.Eff.run comp oracle)
                0
                oracle)
            ~st:!st_ref
            ~oracle
        in
        st_ref := st;
        res)
      (tys, errs, warns, st_ref)
  in
  !tys, !errs, !warns, !st_ref
;;
