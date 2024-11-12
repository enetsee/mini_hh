open Common
open Reporting

type tell =
  | Prop
  | Cstr
  | All
  | Any

let show_tell = function
  | Prop -> "prop"
  | Cstr -> "cstr"
  | All -> "all"
  | Any -> "any"
;;

type enter_tell_prop =
  { prop : Prop.t
  ; ctxt_cont : Ctxt.Cont.t
  }

type enter_tell_cstr =
  { cstr : Cstr.t
  ; ctxt_cont : Ctxt.Cont.t
  }

type enter_tell_all =
  { props : Prop.t list
  ; errs : Err.t list
  ; ctxt_cont : Ctxt.Cont.t
  }

type enter_tell_any =
  { props : Prop.t list
  ; errs : Err.t list
  ; ctxt_cont : Ctxt.Cont.t
  }

type exit_tell =
  { tell : tell
  ; err_opt : Err.t option
  }

type ask_up =
  { of_ : Ty.Ctor.t
  ; at : Name.Ctor.t
  }

type _ Effect.t +=
  | Ask_up : ask_up -> Oracle.Classish.instantiation Effect.t
  | Ask_ty_param_variances :
      Name.Ctor.t
      -> Variance.t Located.t list option Effect.t
  | Log_enter_tell_prop : enter_tell_prop -> (Prop.t * Ctxt.Cont.t) Effect.t
  | Log_enter_tell_cstr : enter_tell_cstr -> (Cstr.t * Ctxt.Cont.t) Effect.t
  | Log_enter_tell_all :
      enter_tell_all
      -> (Prop.t list * Err.t list * Ctxt.Cont.t) Effect.t
  | Log_enter_tell_any :
      enter_tell_any
      -> (Prop.t list * Err.t list * Ctxt.Cont.t) Effect.t
  | Log_exit_tell : exit_tell -> Err.t option Effect.t

let ask_up ~of_ ~at = Effect.perform (Ask_up { of_; at })
let ask_ty_param_variances ctor = Effect.perform (Ask_ty_param_variances ctor)

let log_enter_tell_prop prop ctxt_cont =
  Effect.perform (Log_enter_tell_prop { prop; ctxt_cont })
;;

let log_enter_tell_cstr cstr ctxt_cont =
  Effect.perform (Log_enter_tell_cstr { cstr; ctxt_cont })
;;

let log_enter_tell_all props errs ctxt_cont =
  Effect.perform (Log_enter_tell_all { props; errs; ctxt_cont })
;;

let log_enter_tell_any props errs ctxt_cont =
  Effect.perform (Log_enter_tell_any { props; errs; ctxt_cont })
;;

let log_exit_tell tell err_opt =
  Effect.perform (Log_exit_tell { tell; err_opt })
;;

let log_exit_tell_prop = log_exit_tell Prop
let log_exit_tell_cstr = log_exit_tell Cstr
let log_exit_tell_all = log_exit_tell All
let log_exit_tell_any = log_exit_tell Any

let run comp oracle =
  Effect.Deep.match_with
    comp
    ()
    { effc =
        (fun (type a) (eff : a Effect.t) ->
          match eff with
          | Ask_up { of_; at } ->
            let inst = Oracle.up oracle ~of_ ~at in
            Some
              (fun (k : (a, _) Effect.Deep.continuation) ->
                Effect.Deep.continue k inst)
          | Ask_ty_param_variances ctor ->
            let ty_param_vars_opt = Oracle.param_variances_opt oracle ~ctor in
            Some
              (fun (k : (a, _) Effect.Deep.continuation) ->
                Effect.Deep.continue k ty_param_vars_opt)
          | Log_enter_tell_prop { prop; ctxt_cont } ->
            Some
              (fun (k : (a, _) Effect.Deep.continuation) ->
                Effect.Deep.continue k (prop, ctxt_cont))
          | Log_enter_tell_cstr { cstr; ctxt_cont } ->
            Some
              (fun (k : (a, _) Effect.Deep.continuation) ->
                Effect.Deep.continue k (cstr, ctxt_cont))
          | Log_enter_tell_all { props; errs; ctxt_cont } ->
            Some
              (fun (k : (a, _) Effect.Deep.continuation) ->
                Effect.Deep.continue k (props, errs, ctxt_cont))
          | Log_enter_tell_any { props; errs; ctxt_cont } ->
            Some
              (fun (k : (a, _) Effect.Deep.continuation) ->
                Effect.Deep.continue k (props, errs, ctxt_cont))
          | Log_exit_tell { err_opt; _ } ->
            Some
              (fun (k : (a, _) Effect.Deep.continuation) ->
                Effect.Deep.continue k err_opt)
          | _ -> None)
    ; retc = (fun res -> res)
    ; exnc = (fun exn -> raise exn)
    }
;;
