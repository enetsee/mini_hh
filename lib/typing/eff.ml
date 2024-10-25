open Reporting

type _ Effect.t +=
  | Log_error : Err.t -> unit Effect.t
  | Log_warning : Warn.t -> unit Effect.t
  | Tell_is_subtype :
      { ty_sub : Ty.t
      ; ty_super : Ty.t
      ; cont_ctxt : Ctxt.Cont.t
      }
      -> bool option Effect.t
  | (* | Find_local : Name.Tm_var.t -> Ty.t option Effect.t | Locally_refine : { is_opt : Ctxt.Cont.Refinement.t option
       ; as_opt : Ctxt.Cont.Refinement.t option } -> unit Effect.t | Refine_by : { ty_scrut : Ty.t ; ty_test : Ty.t } ->
       (Ty.Refinement.t * Ctxt.Ty_param.Refinement.t option) Effect.t *)
    (* | Locally_bind_ty_params : Ty.Param.t list -> unit Effect.t *)
      Locally_enter_classish :
      { name : Name.Ctor.t Located.t
      ; this : Ty.Param_bounds.t
      }
      -> unit Effect.t

let log_error err = Effect.perform (Log_error err)
let log_warning warn = Effect.perform (Log_warning warn)
let tell_is_subtype ~ty_sub ~ty_super cont_ctxt = Effect.perform (Tell_is_subtype { ty_sub; ty_super; cont_ctxt })

(* let find_local tm_var = Effect.perform (Find_local tm_var) let locally_refine ~is_opt ~as_opt = Effect.perform
   (Locally_refine { is_opt; as_opt }) let refine_by ~ty_scrut ~ty_test = Effect.perform (Refine_by { ty_scrut; ty_test
   }) let locally_bind_ty_params ty_params = Effect.perform (Locally_bind_ty_params ty_params) *)
let locally_enter_classish ~name ~this = Effect.perform (Locally_enter_classish { name; this })
