open Core
open Common
open Reporting

type _ Effect.t +=
  | Gen_fresh_ty_params : int -> Name.Ty_param.t list Effect.t (** Get n globally fresh type parameter names *)
  | Ask_up :
      { of_ : Ty.Ctor.t
      ; at : Name.Ctor.t
      }
      -> Ty.t list option Effect.t
      (** Get the instantation of the constructor type [of_] at a superclass given by the constructor [at]. This will be
          [None] if [of_] does not extend or implement [at] *)
  | Ask_down :
      { of_ : Ty.Ctor.t
      ; at : Name.Ctor.t
      }
      -> Ty.t list option Effect.t
      (** Get the instantation of the constructor type [of_] at a subclass given by the constructor [at]. This will be
          [None] if [at] does not extend or implement [of_] *)
  | Ask_ty_param_variances : Name.Ctor.t -> Variance.t Located.t list option Effect.t
      (** Get the declared variances for the type parameters of a constructor name. The will be [None] is the
          constructor is not bound*)

let gen_fresh_ty_params n = Effect.perform (Gen_fresh_ty_params n)
let ask_up ~of_ ~at = Effect.perform (Ask_up { of_; at })
let ask_down ~of_ ~at = Effect.perform (Ask_down { of_; at })
let ask_ty_param_variances ctor = Effect.perform (Ask_ty_param_variances ctor)

let run comp src oracle =
  let src_ref = ref src in
  Effect.Deep.match_with
    comp
    ()
    { effc =
        (fun (type a) (eff : a Effect.t) ->
          match eff with
          (* ~~ Generate [n] globally fresh type parameter names using a global source ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
          | Gen_fresh_ty_params n ->
            let offset = !src_ref in
            src_ref := offset + n;
            let names = List.init n ~f:(fun i -> Name.Ty_param.of_string @@ Format.sprintf {|T#%n|} (i + offset)) in
            Some (fun (k : (a, _) Effect.Deep.continuation) -> Effect.Deep.continue k names)
          | Ask_up { of_; at } ->
            let ty_args_opt = Oracle.up oracle ~of_ ~at in
            Some (fun (k : (a, _) Effect.Deep.continuation) -> Effect.Deep.continue k ty_args_opt)
          | Ask_down { of_; at } ->
            let ty_args_opt = Oracle.down oracle ~of_ ~at in
            Some (fun (k : (a, _) Effect.Deep.continuation) -> Effect.Deep.continue k ty_args_opt)
          | Ask_ty_param_variances ctor ->
            let ty_param_vars_opt = Oracle.param_variances_opt oracle ~ctor in
            Some (fun (k : (a, _) Effect.Deep.continuation) -> Effect.Deep.continue k ty_param_vars_opt)
          | _ -> None)
    ; retc = (fun res -> res, !src_ref)
    ; exnc = (fun exn -> raise exn)
    }
;;
