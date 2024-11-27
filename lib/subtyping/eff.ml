open Core
open Common
open Reporting

type tell =
  | Prop
  | Cstr
  | All
  | Any

type upper_or_lower =
  | Upper
  | Lower

let show_upper_or_lower = function
  | Upper -> "upper"
  | Lower -> "lower"
;;

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

type add_bound =
  { var : Ty.Var.t
  ; bound : Ty.t
  ; upper_or_lower : upper_or_lower
  }

type get_bounds =
  { var : Ty.Var.t
  ; upper_or_lower : upper_or_lower
  }

type observe_variance =
  { var : Ty.Var.t
  ; variance : Common.Variance.t
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
  | Add_bound : add_bound -> unit Effect.t
  | Get_bounds : get_bounds -> Ty.t list Effect.t
  | Get_fresh_tyvar : Prov.t -> Ty.t Effect.t
  | Observe_variance : observe_variance -> unit Effect.t
  | Request_fresh_ty_params : int -> Name.Ty_param.t list Effect.t

let request_fresh_ty_params n = Effect.perform (Request_fresh_ty_params n)

let observe_variance var ~variance =
  Effect.perform (Observe_variance { var; variance })
;;

let get_fresh_tyvar prov = Effect.perform (Get_fresh_tyvar prov)

let add_upper_bound var ~bound =
  Effect.perform (Add_bound { var; bound; upper_or_lower = Upper })
;;

let add_lower_bound var ~bound =
  Effect.perform (Add_bound { var; bound; upper_or_lower = Lower })
;;

let get_upper_bounds var =
  Effect.perform (Get_bounds { var; upper_or_lower = Upper })
;;

let get_lower_bounds var =
  Effect.perform (Get_bounds { var; upper_or_lower = Lower })
;;

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

let run comp ~st ~src ~oracle =
  let st_ref = ref st in
  let src_ref = ref src in
  Effect.Deep.match_with
    comp
    ()
    { effc =
        (fun (type a) (eff : a Effect.t) ->
          match eff with
          | Add_bound { var; bound; upper_or_lower = Upper } ->
            let st = State.add_upper_bound !st_ref ~var ~bound in
            st_ref := st;
            Some
              (fun (k : (a, _) Effect.Deep.continuation) ->
                Effect.Deep.continue k ())
          | Add_bound { var; bound; upper_or_lower = Lower } ->
            let st = State.add_lower_bound !st_ref ~var ~bound in
            st_ref := st;
            Some
              (fun (k : (a, _) Effect.Deep.continuation) ->
                Effect.Deep.continue k ())
          | Observe_variance { var; variance } ->
            let st = State.observe_variance_exn !st_ref ~var ~variance in
            st_ref := st;
            Some
              (fun (k : (a, _) Effect.Deep.continuation) ->
                Effect.Deep.continue k ())
          | Get_bounds { var; upper_or_lower = Upper } ->
            let bounds = State.get_upper_bounds_exn !st_ref ~var in
            Some
              (fun (k : (a, _) Effect.Deep.continuation) ->
                Effect.Deep.continue k bounds)
          | Get_bounds { var; upper_or_lower = Lower } ->
            let bounds = State.get_lower_bounds_exn !st_ref ~var in
            Some
              (fun (k : (a, _) Effect.Deep.continuation) ->
                Effect.Deep.continue k bounds)
          | Get_fresh_tyvar prov ->
            let ty, st = State.fresh_tyvar !st_ref ~prov in
            st_ref := st;
            Some
              (fun (k : (a, _) Effect.Deep.continuation) ->
                Effect.Deep.continue k ty)
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
          | Request_fresh_ty_params n ->
            let offset = !src_ref in
            src_ref := offset + n;
            let names =
              List.init n ~f:(fun i ->
                Name.Ty_param.of_string @@ Format.sprintf {|T#%n|} (i + offset))
            in
            Some
              (fun (k : (a, _) Effect.Deep.continuation) ->
                Effect.Deep.continue k names)
          | _ -> None)
    ; retc = (fun res -> res, !st_ref, !src_ref)
    ; exnc = (fun exn -> raise exn)
    }
;;
