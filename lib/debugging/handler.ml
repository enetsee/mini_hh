open Reporting

(** A very long, very boring effect handler which simply lifts the payload of each effect in a corresponding status.
    Unfortunately, I don't think there is a way of composing 'debug' handlers without modifying the program to indicate
    when we are 'wrapping' an effectful computation. I'm still looking at other ways but, for now, the manual approach
    works fine even if it's a bit labour intensive and slightly error prone. *)
let run comp =
  let status =
    Effect.Deep.match_with
      comp
      ()
      { effc =
          (fun (type a) (eff : a Effect.t) ->
            match eff with
            | Typing.Eff.Log_error data ->
              Some
                (fun (k : (a, _) Effect.Deep.continuation) ->
                  Status.(Typing (Logged_error { data; k })))
            | Typing.Eff.Log_warning data ->
              Some
                (fun (k : (a, _) Effect.Deep.continuation) ->
                  Status.(Typing (Logged_warning { data; k })))
            | Typing.Eff.Log_enter_synth_expr data ->
              Some
                (fun (k : (a, _) Effect.Deep.continuation) ->
                  Status.(Typing (Logged_enter_synth_expr { data; k })))
            | Typing.Eff.Log_enter_check_expr data ->
              Some
                (fun (k : (a, _) Effect.Deep.continuation) ->
                  Status.(Typing (Logged_enter_check_expr { data; k })))
            | Typing.Eff.Log_exit_expr data ->
              Some
                (fun (k : (a, _) Effect.Deep.continuation) ->
                  Status.(Typing (Logged_exit_expr { data; k })))
            | Typing.Eff.Log_enter_stmt data ->
              Some
                (fun (k : (a, _) Effect.Deep.continuation) ->
                  Status.(Typing (Logged_enter_stmt { data; k })))
            | Typing.Eff.Log_exit_stmt data ->
              Some
                (fun (k : (a, _) Effect.Deep.continuation) ->
                  Status.(Typing (Logged_exit_stmt { data; k })))
            | Typing.Eff.Log_enter_classish_def data ->
              Some
                (fun (k : (a, _) Effect.Deep.continuation) ->
                  Status.(Typing (Logged_enter_classish_def { data; k })))
            | Typing.Eff.Log_exit_classish_def data ->
              Some
                (fun (k : (a, _) Effect.Deep.continuation) ->
                  Status.(Typing (Logged_exit_classish_def { data; k })))
            | Typing.Eff.Log_enter_fn_def data ->
              Some
                (fun (k : (a, _) Effect.Deep.continuation) ->
                  Status.(Typing (Logged_enter_fn_def { data; k })))
            | Typing.Eff.Log_exit_fn_def data ->
              Some
                (fun (k : (a, _) Effect.Deep.continuation) ->
                  Status.(Typing (Logged_exit_fn_def { data; k })))
            | Typing.Eff.Get_fresh_tyvar data ->
              Some
                (fun (k : (a, _) Effect.Deep.continuation) ->
                  Status.(Typing (Got_fresh_tyvar { data; k })))
            | Typing.Eff.Ask_id data ->
              Some
                (fun (k : (a, _) Effect.Deep.continuation) ->
                  Status.(Typing (Asked_id { data; k })))
            | Refinement.Eff.Request_fresh_ty_params data ->
              Some
                (fun (k : (a, _) Effect.Deep.continuation) ->
                  Status.(Refinement (Requested_fresh_ty_params { data; k })))
            | Refinement.Eff.Ask_up data ->
              Some
                (fun (k : (a, _) Effect.Deep.continuation) ->
                  Status.(Refinement (Asked_up { data; k })))
            | Refinement.Eff.Ask_ty_param_variances data ->
              Some
                (fun (k : (a, _) Effect.Deep.continuation) ->
                  Status.(Refinement (Asked_ty_param_variance { data; k })))
            | Refinement.Eff.Log_exit data ->
              Some
                (fun (k : (a, _) Effect.Deep.continuation) ->
                  Status.(Refinement (Logged_exit { data; k })))
            | Refinement.Eff.Log_enter_refinement data ->
              Some
                (fun (k : (a, _) Effect.Deep.continuation) ->
                  Status.(Refinement (Logged_enter_refinement { data; k })))
            | Refinement.Eff.Log_enter_ty data ->
              Some
                (fun (k : (a, _) Effect.Deep.continuation) ->
                  Status.(Refinement (Logged_enter_ty { data; k })))
            | Refinement.Eff.Log_enter_existential_scrut data ->
              Some
                (fun (k : (a, _) Effect.Deep.continuation) ->
                  Status.(
                    Refinement (Logged_enter_existential_scrut { data; k })))
            | Refinement.Eff.Log_enter_existential_test data ->
              Some
                (fun (k : (a, _) Effect.Deep.continuation) ->
                  Status.(
                    Refinement (Logged_enter_existential_test { data; k })))
            | Refinement.Eff.Log_enter_union_scrut data ->
              Some
                (fun (k : (a, _) Effect.Deep.continuation) ->
                  Status.(Refinement (Logged_enter_union_scrut { data; k })))
            | Refinement.Eff.Log_enter_union_test data ->
              Some
                (fun (k : (a, _) Effect.Deep.continuation) ->
                  Status.(Refinement (Logged_enter_union_test { data; k })))
            | Refinement.Eff.Log_enter_inter_scrut data ->
              Some
                (fun (k : (a, _) Effect.Deep.continuation) ->
                  Status.(Refinement (Logged_enter_inter_scrut { data; k })))
            | Refinement.Eff.Log_enter_inter_test data ->
              Some
                (fun (k : (a, _) Effect.Deep.continuation) ->
                  Status.(Refinement (Logged_enter_inter_test { data; k })))
            | Refinement.Eff.Log_enter_top_level_generic_scrut data ->
              Some
                (fun (k : (a, _) Effect.Deep.continuation) ->
                  Status.(
                    Refinement
                      (Logged_enter_top_level_generic_scrut { data; k })))
            | Refinement.Eff.Log_enter_top_level_generic_test data ->
              Some
                (fun (k : (a, _) Effect.Deep.continuation) ->
                  Status.(
                    Refinement (Logged_enter_top_level_generic_test { data; k })))
            | Refinement.Eff.Log_enter_ctor data ->
              Some
                (fun (k : (a, _) Effect.Deep.continuation) ->
                  Status.(Refinement (Logged_enter_ctor { data; k })))
            | Refinement.Eff.Log_enter_ctor_arg data ->
              Some
                (fun (k : (a, _) Effect.Deep.continuation) ->
                  Status.(Refinement (Logged_enter_ctor_arg { data; k })))
            | Exposure.Eff.Ask_up data ->
              Some
                (fun (k : (a, _) Effect.Deep.continuation) ->
                  Status.(Exposure (Asked_up { data; k })))
            | Exposure.Eff.Ask_ctor data ->
              Some
                (fun (k : (a, _) Effect.Deep.continuation) ->
                  Status.(Exposure (Asked_ctor { data; k })))
            | Exposure.Eff.Log_enter_delta data ->
              Some
                (fun (k : (a, _) Effect.Deep.continuation) ->
                  Status.(Exposure (Logged_enter_delta { data; k })))
            | Exposure.Eff.Log_exit_delta data ->
              Some
                (fun (k : (a, _) Effect.Deep.continuation) ->
                  Status.(Exposure (Logged_exit_delta { data; k })))
            | Exposure.Eff.Log_enter_cont_delta data ->
              Some
                (fun (k : (a, _) Effect.Deep.continuation) ->
                  Status.(Exposure (Logged_enter_cont_delta { data; k })))
            | Exposure.Eff.Log_exit_cont_delta data ->
              Some
                (fun (k : (a, _) Effect.Deep.continuation) ->
                  Status.(Exposure (Logged_exit_cont_delta { data; k })))
            | Exposure.Eff.Log_exit_elem data ->
              Some
                (fun (k : (a, _) Effect.Deep.continuation) ->
                  Status.(Exposure (Logged_exit_elem { data; k })))
            | Exposure.Eff.Log_enter_ty data ->
              Some
                (fun (k : (a, _) Effect.Deep.continuation) ->
                  Status.(Exposure (Logged_enter_ty { data; k })))
            | Exposure.Eff.Log_enter_generic data ->
              Some
                (fun (k : (a, _) Effect.Deep.continuation) ->
                  Status.(Exposure (Logged_enter_generic { data; k })))
            | Exposure.Eff.Log_enter_union data ->
              Some
                (fun (k : (a, _) Effect.Deep.continuation) ->
                  Status.(Exposure (Logged_enter_union { data; k })))
            | Exposure.Eff.Log_enter_inter data ->
              Some
                (fun (k : (a, _) Effect.Deep.continuation) ->
                  Status.(Exposure (Logged_enter_inter { data; k })))
            | Exposure.Eff.Log_enter_fn data ->
              Some
                (fun (k : (a, _) Effect.Deep.continuation) ->
                  Status.(Exposure (Logged_enter_fn { data; k })))
            | Exposure.Eff.Log_enter_tuple data ->
              Some
                (fun (k : (a, _) Effect.Deep.continuation) ->
                  Status.(Exposure (Logged_enter_tuple { data; k })))
            | Exposure.Eff.Log_enter_ctor data ->
              Some
                (fun (k : (a, _) Effect.Deep.continuation) ->
                  Status.(Exposure (Logged_enter_ctor { data; k })))
            | Exposure.Eff.Log_enter_exists data ->
              Some
                (fun (k : (a, _) Effect.Deep.continuation) ->
                  Status.(Exposure (Logged_enter_exists { data; k })))
            | Subtyping.Eff.Ask_up data ->
              Some
                (fun (k : (a, _) Effect.Deep.continuation) ->
                  Status.(Subtyping (Asked_up { data; k })))
            | Subtyping.Eff.Ask_ty_param_variances data ->
              Some
                (fun (k : (a, _) Effect.Deep.continuation) ->
                  Status.(Subtyping (Asked_ty_param_variances { data; k })))
            | Subtyping.Eff.Log_enter_tell_prop data ->
              Some
                (fun (k : (a, _) Effect.Deep.continuation) ->
                  Status.(Subtyping (Logged_enter_tell_prop { data; k })))
            | Subtyping.Eff.Log_enter_tell_cstr data ->
              Some
                (fun (k : (a, _) Effect.Deep.continuation) ->
                  Status.(Subtyping (Logged_enter_tell_cstr { data; k })))
            | Subtyping.Eff.Log_enter_tell_all data ->
              Some
                (fun (k : (a, _) Effect.Deep.continuation) ->
                  Status.(Subtyping (Logged_enter_tell_all { data; k })))
            | Subtyping.Eff.Log_enter_tell_any data ->
              Some
                (fun (k : (a, _) Effect.Deep.continuation) ->
                  Status.(Subtyping (Logged_enter_tell_any { data; k })))
            | Subtyping.Eff.Log_exit_tell data ->
              Some
                (fun (k : (a, _) Effect.Deep.continuation) ->
                  Status.(Subtyping (Logged_exit_tell { data; k })))
            | Subtyping.Eff.Add_instantiation data ->
              Some
                (fun (k : (a, _) Effect.Deep.continuation) ->
                  Status.(Subtyping (Added_instantiation { data; k })))
            | Subtyping.Eff.Add_bound data ->
              Some
                (fun (k : (a, _) Effect.Deep.continuation) ->
                  Status.(Subtyping (Added_bound { data; k })))
            | Subtyping.Eff.Get_bounds data ->
              Some
                (fun (k : (a, _) Effect.Deep.continuation) ->
                  Status.(Subtyping (Got_bounds { data; k })))
            | Subtyping.Eff.Get_fresh_tyvar data ->
              Some
                (fun (k : (a, _) Effect.Deep.continuation) ->
                  Status.(Subtyping (Got_fresh_tyvar { data; k })))
            | Subtyping.Eff.Observe_variance data ->
              Some
                (fun (k : (a, _) Effect.Deep.continuation) ->
                  Status.(Subtyping (Observed_variance { data; k })))
            | Subtyping.Eff.Request_fresh_ty_params data ->
              Some
                (fun (k : (a, _) Effect.Deep.continuation) ->
                  Status.(Subtyping (Requested_fresh_ty_params { data; k })))
            | _ -> None)
      ; retc = (fun _res -> Status.Completed)
      ; exnc = (fun exn -> Status.Failed exn)
      }
  in
  let span, ctxt_def, ctxt_cont =
    match status with
    | Status.Typing
        (Status.Typing_status.Logged_enter_classish_def
          { data = { classish_def; ctxt_def; ctxt_cont }; _ }) ->
      Located.span_of classish_def, ctxt_def, ctxt_cont
    | Status.Typing
        (Status.Typing_status.Logged_enter_fn_def
          { data = { fn_def; ctxt_def; ctxt_cont }; _ }) ->
      Located.span_of fn_def, ctxt_def, ctxt_cont
    | _ ->
      failwith
        "Debug.Handler: did not enter debugging through either classish \
         definition or function definition"
  in
  let state = State.empty in
  Step.create ~status ~state ~span ~ctxt_def ~ctxt_cont
;;
