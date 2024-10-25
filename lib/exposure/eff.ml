open Core

type _ Effect.t +=
  | Ask_up :
      { of_ : Ty.Ctor.t
      ; at : Name.Ctor.t
      }
      -> Ty.t list option Effect.t
      (** Get the instantation of the constructor type [of_] at a superclass given by the constructor [at]. This will be
          [None] if [of_] does not extend or implement [at] *)
  | Ask_ctor : Name.Ctor.t -> (Lang.Ty_param_def.t list * Ty.t list Name.Ctor.Map.t) option Effect.t

let ask_up ~of_ ~at = Effect.perform (Ask_up { of_; at })
let ask_ctor nm = Effect.perform (Ask_ctor nm)

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
          | Ask_ctor nm ->
            let ty_params_supers = Oracle.find_ctor oracle nm in
            Some (fun (k : (a, _) Effect.Deep.continuation) -> Effect.Deep.continue k ty_params_supers)
          | _ -> None)
    ; retc = (fun res -> res)
    ; exnc = (fun exn -> raise exn)
    }
;;
