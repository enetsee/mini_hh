open Core

(* We can always synthesize a type for a literal *)
let synth lit =
  match lit with
  | Lang.Lit.Bool _ -> Ty.bool Reporting.Prov.empty
;;

let check lit ~against ~env ~ctxt =
  (* Subsumption case - sythesize a type (`ty`) then generate the subtype constraint  `ty <: against` *)
  let ty_sub = synth lit in
  let subtyping_res =
    (* TODO(mjt) move to algebraic effects and hide all this *)
    let Envir.Typing.{ ty_param; ty_param_refine; subtyping = env; _ } = env
    and Ctxt.{ oracle; _ } = ctxt in
    let ctxt = Subtyping.Ctxt.create ~oracle ~ty_param ~ty_param_refine ()
    and ty_super = against in
    Subtyping.Tell.is_subtype ~ty_sub ~ty_super ~ctxt ~env
  in
  (* If the subtyping constraint gave an error, return the original environment otherwise update it with the
     modified subtyping env *)
  match subtyping_res with
  | Error err -> Error (Err.Subtyping err)
  | Ok subtyping_env -> Ok Envir.Typing.{ env with subtyping = subtyping_env }
;;
