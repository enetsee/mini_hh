open Common
open Reporting

type tell =
  | Prop
  | Cstr
  | All
  | Any

type is_subtype_step =
  | Ty
  | Ctor
  | Ctor_args
  | Tuple
  | Tuple_args

type _ Effect.t +=
  | Ask_up :
      { of_ : Ty.Ctor.t
      ; at : Name.Ctor.t
      }
      -> Ty.t list option Effect.t
      (** Get the instantation of the constructor type [of_] at a superclass given by the constructor [at]. This will be
          [None] if [of_] does not extend or implement [at] *)
  | Ask_ty_param_variances : Name.Ctor.t -> Variance.t Located.t list option Effect.t
      (** Get the declared variances for the type parameters of a constructor name. The will be [None] is the
          constructor is not bound*)
  | Log_enter_tell_prop :
      { prop : Prop.t
      ; ctxt_cont : Ctxt.Cont.t
      }
      -> (Prop.t * Ctxt.Cont.t) Effect.t
  | Log_enter_tell_cstr :
      { cstr : Cstr.t
      ; ctxt_cont : Ctxt.Cont.t
      }
      -> (Cstr.t * Ctxt.Cont.t) Effect.t
  | Log_enter_tell_all :
      { props : Prop.t list
      ; errs : Err.t list
      ; ctxt_cont : Ctxt.Cont.t
      }
      -> (Cstr.t * Ctxt.Cont.t) Effect.t
  | Log_enter_tell_any :
      { props : Prop.t list
      ; errs : Err.t list
      ; ctxt_cont : Ctxt.Cont.t
      }
      -> (Cstr.t * Ctxt.Cont.t) Effect.t
  | Log_exit_tell :
      { which : tell
      ; err_opt : Err.t option
      }
      -> Err.t option Effect.t

let ask_up ~of_ ~at = Effect.perform (Ask_up { of_; at })
let ask_ty_param_variances ctor = Effect.perform (Ask_ty_param_variances ctor)

let run comp oracle =
  Effect.Deep.match_with
    comp
    ()
    { effc =
        (fun (type a) (eff : a Effect.t) ->
          match eff with
          | Ask_up { of_; at } ->
            let ty_args_opt = Oracle.up oracle ~of_ ~at in
            Some (fun (k : (a, _) Effect.Deep.continuation) -> Effect.Deep.continue k ty_args_opt)
          | Ask_ty_param_variances ctor ->
            let ty_param_vars_opt = Oracle.param_variances_opt oracle ~ctor in
            Some (fun (k : (a, _) Effect.Deep.continuation) -> Effect.Deep.continue k ty_param_vars_opt)
          | _ -> None)
    ; retc = (fun res -> res)
    ; exnc = (fun exn -> raise exn)
    }
;;
