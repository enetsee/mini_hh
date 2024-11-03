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

module Debug = struct
  module State = struct
    module Minimal = struct
      type t =
        { current_span : Span.t
        ; tys : (Span.t * Ty.t) list
        ; errs : Err.t list
        ; warns : Warn.t list
        ; ty_param_name_source : int
        }
      [@@deriving create]

      let init span = { current_span = span; tys = []; errs = []; warns = []; ty_param_name_source = 0 }

      let pp ppf t =
        Fmt.(
          vbox
          @@ record
               ~sep:cut
               [ field "types" (fun { tys; _ } -> tys) @@ vbox @@ list ~sep:cut @@ pair ~sep:sp Span.pp Ty.pp
               ; field "errors" (fun { errs; _ } -> errs) @@ vbox @@ list ~sep:cut Err.pp
               ; field "warnings " (fun { warns; _ } -> warns) @@ vbox @@ list ~sep:cut Warn.pp
               ; field "type parameter name source" (fun { ty_param_name_source; _ } -> ty_param_name_source) int
               ])
          ppf
          t
      ;;
    end

    include Minimal
    include Pretty.Make (Minimal)

    let add_error t err = { t with errs = err :: t.errs }
    let add_warning t warn = { t with warns = warn :: t.warns }
    let add_ty_span t ty span = { t with tys = (span, ty) :: t.tys }

    let fresh_ty_params t n =
      let { ty_param_name_source; _ } = t in
      let offset = ty_param_name_source in
      let ty_param_name_source = offset + n in
      let names = List.init n ~f:(fun i -> Name.Ty_param.of_string @@ Format.sprintf {|T#%n|} (i + offset)) in
      { t with ty_param_name_source }, names
    ;;

    let update_span t ~span = { t with current_span = span }
  end

  module Status = struct
    module Minimal = struct
      type t =
        | Entered_expr of
            { span : Span.t
            ; ctxt_def : Ctxt.Def.t
            ; ctxt_cont : Ctxt.Cont.t
            ; k : (Ctxt.Def.t * Ctxt.Cont.t, t) Effect.Deep.continuation [@show.opaque]
            }
        | Exited_expr of
            { span : Span.t
            ; ty : Ty.t
            ; expr_delta : Ctxt.Cont.Expr_delta.t
            ; k : (Ty.t * Ctxt.Cont.Expr_delta.t, t) Effect.Deep.continuation [@show.opaque]
            }
        | Entered_stmt of
            { span : Span.t
            ; ctxt_def : Ctxt.Def.t
            ; ctxt_cont : Ctxt.Cont.t
            ; k : (Ctxt.Def.t * Ctxt.Cont.t, t) Effect.Deep.continuation [@show.opaque]
            }
        | Exited_stmt of
            { span : Span.t
            ; delta : Ctxt.Delta.t
            ; k : (Ctxt.Delta.t, t) Effect.Deep.continuation [@show.opaque]
            }
        | Entered_classish_def of
            { span : Span.t
            ; name : Name.Ctor.t
            ; ctxt_def : Ctxt.Def.t
            ; ctxt_cont : Ctxt.Cont.t
            ; k : (Ctxt.Def.t * Ctxt.Cont.t, t) Effect.Deep.continuation [@show.opaque]
            }
        | Exited_classish_def of
            { span : Span.t
            ; k : (unit, t) Effect.Deep.continuation [@show.opaque]
            }
        | Entered_fn_def of
            { span : Span.t
            ; name : Name.Fn.t
            ; ctxt_def : Ctxt.Def.t
            ; ctxt_cont : Ctxt.Cont.t
            ; k : (Ctxt.Def.t * Ctxt.Cont.t, t) Effect.Deep.continuation [@show.opaque]
            }
        | Exited_fn_def of
            { span : Span.t
            ; k : (unit, t) Effect.Deep.continuation [@show.opaque]
            }
        | Raised_error of
            { err : Err.t
            ; k : (unit, t) Effect.Deep.continuation [@show.opaque]
            }
        | Raised_warning of
            { warn : Warn.t
            ; k : (unit, t) Effect.Deep.continuation [@show.opaque]
            }
        (* ~~ Refinement ~~ *)
        | Entered_refinement of
            { ty_test : Ty.t
            ; ty_scrut : Ty.t
            ; ctxt_cont : Ctxt.Cont.t
            ; k : (Ty.t * Ty.t * Ctxt.Cont.t, t) Effect.Deep.continuation [@show.opaque]
            }
        | Exited_refinement of
            { ty_rfmt : Ty.Refinement.t
            ; ty_param_rfmt_opt : (Prov.t * Ctxt.Ty_param.Refinement.t) option
            ; k : (Ty.Refinement.t * (Prov.t * Ctxt.Ty_param.Refinement.t) option, t) Effect.Deep.continuation
                 [@show.opaque]
            }
        | Entered_refine_ty of
            { ty_test : Ty.t
            ; ty_scrut : Ty.t
            ; ctxt_cont : Ctxt.Cont.t
            ; k : (Ty.t * Ty.t * Ctxt.Cont.t, t) Effect.Deep.continuation [@show.opaque]
            }
        | Exited_refine_ty of
            { ty_rfmt : Ty.Refinement.t
            ; ty_param_rfmt_opt : (Prov.t * Ctxt.Ty_param.Refinement.t) option
            ; k : (Ty.Refinement.t * (Prov.t * Ctxt.Ty_param.Refinement.t) option, t) Effect.Deep.continuation
                 [@show.opaque]
            }
        | Entered_refine_existential_scrut of
            { prov_scrut : Prov.t
            ; ty_exists : Ty.Exists.t
            ; ty_test : Ty.t
            ; ctxt_cont : Ctxt.Cont.t
            ; k : (Prov.t * Ty.Exists.t * Ty.t * Ctxt.Cont.t, t) Effect.Deep.continuation [@show.opaque]
            }
        | Exited_refine_existential_scrut of
            { ty_rfmt : Ty.Refinement.t
            ; ty_param_rfmt_opt : (Prov.t * Ctxt.Ty_param.Refinement.t) option
            ; k : (Ty.Refinement.t * (Prov.t * Ctxt.Ty_param.Refinement.t) option, t) Effect.Deep.continuation
                 [@show.opaque]
            }
        | Entered_refine_existential_test of
            { ty_scrut : Ty.t
            ; prov_test : Prov.t
            ; ty_exists : Ty.Exists.t
            ; ctxt_cont : Ctxt.Cont.t
            ; k : (Ty.t * Prov.t * Ty.Exists.t * Ctxt.Cont.t, t) Effect.Deep.continuation [@show.opaque]
            }
        | Exited_refine_existential_test of
            { ty_rfmt : Ty.Refinement.t
            ; ty_param_rfmt_opt : (Prov.t * Ctxt.Ty_param.Refinement.t) option
            ; k : (Ty.Refinement.t * (Prov.t * Ctxt.Ty_param.Refinement.t) option, t) Effect.Deep.continuation
                 [@show.opaque]
            }
        | Entered_refine_union_scrut of
            { prov_scrut : Prov.t
            ; tys_scrut : Ty.t list
            ; ty_test : Ty.t
            ; ctxt_cont : Ctxt.Cont.t
            ; k : (Prov.t * Ty.t list * Ty.t * Ctxt.Cont.t, t) Effect.Deep.continuation [@show.opaque]
            }
        | Exited_refine_union_scrut of
            { ty_rfmt : Ty.Refinement.t
            ; ty_param_rfmt_opt : (Prov.t * Ctxt.Ty_param.Refinement.t) option
            ; k : (Ty.Refinement.t * (Prov.t * Ctxt.Ty_param.Refinement.t) option, t) Effect.Deep.continuation
                 [@show.opaque]
            }
        | Entered_refine_union_test of
            { ty_scrut : Ty.t
            ; prov_test : Prov.t
            ; tys_test : Ty.t list
            ; ctxt_cont : Ctxt.Cont.t
            ; k : (Ty.t * Prov.t * Ty.t list * Ctxt.Cont.t, t) Effect.Deep.continuation [@show.opaque]
            }
        | Exited_refine_union_test of
            { ty_rfmt : Ty.Refinement.t
            ; ty_param_rfmt_opt : (Prov.t * Ctxt.Ty_param.Refinement.t) option
            ; k : (Ty.Refinement.t * (Prov.t * Ctxt.Ty_param.Refinement.t) option, t) Effect.Deep.continuation
                 [@show.opaque]
            }
        | Asked_up of
            { of_ : Ty.Ctor.t
            ; at : Name.Ctor.t
            ; k : (Ty.t list option, t) Effect.Deep.continuation [@show.opaque]
            }
        | Asked_ty_param_variances of
            { ctor : Name.Ctor.t
            ; k : (Variance.t Located.t list option, t) Effect.Deep.continuation [@show.opaque]
            }
        | Requested_fresh_ty_params of
            { n : int
            ; k : (Name.Ty_param.t list, t) Effect.Deep.continuation [@show.opaque]
            }
        | Complete
        | Failed of Exn.t
      [@@deriving variants, show]
    end

    include Minimal
    include Pretty.Make (Minimal)
  end

  module Step = struct
    module Minimal = struct
      type t = Step of Status.t * State.t [@@deriving variants]

      let pp ppf (Step (status, state)) = Fmt.(vbox @@ pair ~sep:cut Status.pp State.pp) ppf (status, state)
    end

    include Minimal

    let current_span (Step (_, state)) = state.State.current_span
    let errors (Step (_, state)) = state.State.errs
    let warnings (Step (_, state)) = state.State.warns
    let status (Step (status, _)) = status
    let state (Step (_, state)) = state

    include Pretty.Make (Minimal)

    let next (Step (status, state)) ~oracle =
      match status with
      | Status.Asked_up { of_; at; k } ->
        let ty_args_opt = Oracle.up oracle ~of_ ~at in
        step (Effect.Deep.continue k ty_args_opt) state
      | Asked_ty_param_variances { ctor; k } ->
        let variances_opt = Oracle.param_variances_opt oracle ~ctor in
        step (Effect.Deep.continue k variances_opt) state
      | Requested_fresh_ty_params { n; k } ->
        let state, names = State.fresh_ty_params state n in
        step (Effect.Deep.continue k names) state
      | Complete -> step Complete state
      | Failed exn -> step (Failed exn) state
      | Raised_error { k; err } ->
        let state = State.add_error state err in
        step (Effect.Deep.continue k ()) state
      | Raised_warning { k; warn } ->
        let state = State.add_warning state warn in
        step (Effect.Deep.continue k ()) state
      (* ~~ Logging effects for typing ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
      | Entered_expr { ctxt_def; ctxt_cont; k; span } ->
        let state = State.update_span state ~span in
        step (Effect.Deep.continue k (ctxt_def, ctxt_cont)) state
      | Exited_expr { ty; expr_delta; k; span } ->
        let state = State.(update_span ~span @@ add_ty_span state ty span) in
        step (Effect.Deep.continue k (ty, expr_delta)) state
      | Entered_stmt { ctxt_def; ctxt_cont; k; span } ->
        let state = State.update_span ~span state in
        step (Effect.Deep.continue k (ctxt_def, ctxt_cont)) state
      | Exited_stmt { delta; k; _ } -> step (Effect.Deep.continue k delta) state
      | Entered_classish_def { ctxt_def; ctxt_cont; k; span; _ } ->
        let state = State.update_span ~span state in
        step (Effect.Deep.continue k (ctxt_def, ctxt_cont)) state
      | Exited_classish_def { k; _ } -> step (Effect.Deep.continue k ()) state
      | Entered_fn_def { ctxt_def; ctxt_cont; k; span; _ } ->
        let state = State.update_span ~span state in
        step (Effect.Deep.continue k (ctxt_def, ctxt_cont)) state
      | Exited_fn_def { k; _ } -> step (Effect.Deep.continue k ()) state
      (* ~~ Logging effects for refinement ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
      | Entered_refinement { ty_test; ty_scrut; ctxt_cont; k } ->
        step (Effect.Deep.continue k (ty_scrut, ty_test, ctxt_cont)) state
      | Exited_refinement { ty_rfmt; ty_param_rfmt_opt; k } ->
        step (Effect.Deep.continue k (ty_rfmt, ty_param_rfmt_opt)) state
      | Entered_refine_ty { ty_test; ty_scrut; ctxt_cont; k } ->
        step (Effect.Deep.continue k (ty_scrut, ty_test, ctxt_cont)) state
      | Exited_refine_ty { ty_rfmt; ty_param_rfmt_opt; k } ->
        step (Effect.Deep.continue k (ty_rfmt, ty_param_rfmt_opt)) state
      | Entered_refine_existential_scrut { prov_scrut; ty_exists; ty_test; ctxt_cont; k } ->
        step (Effect.Deep.continue k (prov_scrut, ty_exists, ty_test, ctxt_cont)) state
      | Exited_refine_existential_scrut { ty_rfmt; ty_param_rfmt_opt; k } ->
        step (Effect.Deep.continue k (ty_rfmt, ty_param_rfmt_opt)) state
      | Entered_refine_existential_test { ty_scrut; prov_test; ty_exists; ctxt_cont; k } ->
        step (Effect.Deep.continue k (ty_scrut, prov_test, ty_exists, ctxt_cont)) state
      | Exited_refine_existential_test { ty_rfmt; ty_param_rfmt_opt; k } ->
        step (Effect.Deep.continue k (ty_rfmt, ty_param_rfmt_opt)) state
      | Entered_refine_union_scrut { prov_scrut; tys_scrut; ty_test; ctxt_cont; k } ->
        step (Effect.Deep.continue k (prov_scrut, tys_scrut, ty_test, ctxt_cont)) state
      | Exited_refine_union_scrut { ty_rfmt; ty_param_rfmt_opt; k } ->
        step (Effect.Deep.continue k (ty_rfmt, ty_param_rfmt_opt)) state
      | Entered_refine_union_test { ty_scrut; prov_test; tys_test; ctxt_cont; k } ->
        step (Effect.Deep.continue k (ty_scrut, prov_test, tys_test, ctxt_cont)) state
      | Exited_refine_union_test { ty_rfmt; ty_param_rfmt_opt; k } ->
        step (Effect.Deep.continue k (ty_rfmt, ty_param_rfmt_opt)) state
    ;;

    let next' step ~oracle =
      let step = next step ~oracle in
      print step;
      step
    ;;
  end

  let go comp =
    let status =
      Effect.Deep.match_with
        comp
        ()
        { effc =
            (fun (type a) (eff : a Effect.t) ->
              match eff with
              | Log_error err -> Some (fun (k : (a, _) Effect.Deep.continuation) -> Status.raised_error ~err ~k)
              | Log_warning warn -> Some (fun (k : (a, _) Effect.Deep.continuation) -> Status.raised_warning ~warn ~k)
              | Log_enter_expr (span, ctxt_def, ctxt_cont) ->
                Some (fun (k : (a, _) Effect.Deep.continuation) -> Status.entered_expr ~span ~ctxt_def ~ctxt_cont ~k)
              | Log_enter_stmt (span, ctxt_def, ctxt_cont) ->
                Some (fun (k : (a, _) Effect.Deep.continuation) -> Status.entered_stmt ~span ~ctxt_def ~ctxt_cont ~k)
              | Log_enter_classish_def (span, name, ctxt_def, ctxt_cont) ->
                Some
                  (fun (k : (a, _) Effect.Deep.continuation) ->
                    Status.entered_classish_def ~span ~name ~ctxt_def ~ctxt_cont ~k)
              | Log_enter_fn_def (span, name, ctxt_def, ctxt_cont) ->
                Some
                  (fun (k : (a, _) Effect.Deep.continuation) ->
                    Status.entered_fn_def ~span ~name ~ctxt_def ~ctxt_cont ~k)
              | Log_exit_expr (span, ty, expr_delta) ->
                Some (fun (k : (a, _) Effect.Deep.continuation) -> Status.exited_expr ~span ~ty ~expr_delta ~k)
              | Log_exit_stmt (span, delta) ->
                Some (fun (k : (a, _) Effect.Deep.continuation) -> Status.exited_stmt ~span ~delta ~k)
              | Log_exit_classish_def span ->
                Some (fun (k : (a, _) Effect.Deep.continuation) -> Status.exited_classish_def ~span ~k)
              | Log_exit_fn_def span ->
                Some (fun (k : (a, _) Effect.Deep.continuation) -> Status.exited_classish_def ~span ~k)
              (* ~~ Refinement ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
              | Refinement.Eff.Log_enter_refinement { ty_test; ty_scrut; ctxt_cont } ->
                Some
                  (fun (k : (a, _) Effect.Deep.continuation) ->
                    Status.entered_refinement ~ty_test ~ty_scrut ~ctxt_cont ~k)
              | Refinement.Eff.Log_exit_refinement { ty_rfmt; ty_param_rfmt_opt } ->
                Some
                  (fun (k : (a, _) Effect.Deep.continuation) -> Status.exited_refinement ~ty_rfmt ~ty_param_rfmt_opt ~k)
              | Refinement.Eff.Log_enter_refine_ty { ty_test; ty_scrut; ctxt_cont } ->
                Some
                  (fun (k : (a, _) Effect.Deep.continuation) ->
                    Status.entered_refine_ty ~ty_test ~ty_scrut ~ctxt_cont ~k)
              | Refinement.Eff.Log_exit_refine_ty { ty_rfmt; ty_param_rfmt_opt } ->
                Some
                  (fun (k : (a, _) Effect.Deep.continuation) -> Status.exited_refine_ty ~ty_rfmt ~ty_param_rfmt_opt ~k)
              | Refinement.Eff.Log_enter_refine_existential_scrut { prov_scrut; ty_exists; ty_test; ctxt_cont } ->
                Some
                  (fun (k : (a, _) Effect.Deep.continuation) ->
                    Status.entered_refine_existential_scrut ~prov_scrut ~ty_exists ~ty_test ~ctxt_cont ~k)
              | Refinement.Eff.Log_exit_refine_existential_scrut { ty_rfmt; ty_param_rfmt_opt } ->
                Some
                  (fun (k : (a, _) Effect.Deep.continuation) ->
                    Status.exited_refine_existential_scrut ~ty_rfmt ~ty_param_rfmt_opt ~k)
              | Refinement.Eff.Log_enter_refine_existential_test { ty_scrut; prov_test; ty_exists; ctxt_cont } ->
                Some
                  (fun (k : (a, _) Effect.Deep.continuation) ->
                    Status.entered_refine_existential_test ~ty_scrut ~prov_test ~ty_exists ~ctxt_cont ~k)
              | Refinement.Eff.Log_exit_refine_existential_test { ty_rfmt; ty_param_rfmt_opt } ->
                Some
                  (fun (k : (a, _) Effect.Deep.continuation) ->
                    Status.exited_refine_existential_test ~ty_rfmt ~ty_param_rfmt_opt ~k)
              | Refinement.Eff.Log_enter_refine_union_scrut { prov_scrut; tys_scrut; ty_test; ctxt_cont } ->
                Some
                  (fun (k : (a, _) Effect.Deep.continuation) ->
                    Status.entered_refine_union_scrut ~prov_scrut ~tys_scrut ~ty_test ~ctxt_cont ~k)
              | Refinement.Eff.Log_exit_refine_union_scrut { ty_rfmt; ty_param_rfmt_opt } ->
                Some
                  (fun (k : (a, _) Effect.Deep.continuation) ->
                    Status.exited_refine_union_scrut ~ty_rfmt ~ty_param_rfmt_opt ~k)
              | Refinement.Eff.Log_enter_refine_union_test { ty_scrut; prov_test; tys_test; ctxt_cont } ->
                Some
                  (fun (k : (a, _) Effect.Deep.continuation) ->
                    Status.entered_refine_union_test ~ty_scrut ~prov_test ~tys_test ~ctxt_cont ~k)
              | Refinement.Eff.Log_exit_refine_union_test { ty_rfmt; ty_param_rfmt_opt } ->
                Some
                  (fun (k : (a, _) Effect.Deep.continuation) ->
                    Status.exited_refine_union_test ~ty_rfmt ~ty_param_rfmt_opt ~k)
              (* ~~ Refinement other ~~ *)
              | Refinement.Eff.Gen_fresh_ty_params n ->
                Some (fun (k : (a, _) Effect.Deep.continuation) -> Status.requested_fresh_ty_params ~n ~k)
              | Refinement.Eff.Ask_up { of_; at } ->
                Some (fun (k : (a, _) Effect.Deep.continuation) -> Status.asked_up ~of_ ~at ~k)
              | Refinement.Eff.Ask_ty_param_variances ctor ->
                Some (fun (k : (a, _) Effect.Deep.continuation) -> Status.asked_ty_param_variances ~ctor ~k)
              | _ -> None)
        ; retc = (fun _res -> Status.complete)
        ; exnc = (fun exn -> Status.failed exn)
        }
    in
    let span =
      match status with
      | Status.Entered_classish_def { span; _ } -> span
      | Status.Entered_fn_def { span; _ } -> span
      | _ -> failwith "Did not enter a class or function def"
    in
    Step.Step (status, State.init span)
  ;;
end
