open Core
open Reporting

type ask_up =
  { of_ : Ty.Ctor.t
  ; at : Name.Ctor.t
  }

type elem =
  | Ty
  | Generic
  | Fn
  | Tuple
  | Ctor
  | Exists
  | Union
  | Inter

type 'a enter =
  { elem : 'a
  ; ty_params : Ctxt.Ty_param.t
  ; dir : Dir.t
  }

type exit =
  { elem : elem
  ; data : (Ty.t, Err.Set.t) result
  }

type _ Effect.t +=
  | Ask_up : ask_up -> Ty.t list option Effect.t
  | Ask_ctor : Name.Ctor.t -> (Lang.Ty_param_def.t list * Ty.t list Name.Ctor.Map.t) option Effect.t
  | Log_enter_delta : Ctxt.Delta.t -> Ctxt.Delta.t Effect.t
  | Log_exit_delta : Ctxt.Delta.t -> Ctxt.Delta.t Effect.t
  | Log_enter_cont_delta : Ctxt.Cont.Delta.t -> Ctxt.Cont.Delta.t Effect.t
  | Log_exit_cont_delta : Ctxt.Cont.Delta.t -> Ctxt.Cont.Delta.t Effect.t
  | Log_exit_elem : exit -> (Ty.t, Err.Set.t) result Effect.t
  | Log_enter_ty : Ty.t enter -> (Ty.t * Ctxt.Ty_param.t * Dir.t) Effect.t
  | Log_enter_generic :
      (Prov.t * Name.Ty_param.t) enter
      -> (Prov.t * Name.Ty_param.t * Ctxt.Ty_param.t * Dir.t) Effect.t
  | Log_enter_union : (Prov.t * Ty.t list) enter -> (Prov.t * Ty.t list * Ctxt.Ty_param.t * Dir.t) Effect.t
  | Log_enter_inter : (Prov.t * Ty.t list) enter -> (Prov.t * Ty.t list * Ctxt.Ty_param.t * Dir.t) Effect.t
  | Log_enter_fn : (Prov.t * Ty.Fn.t) enter -> (Prov.t * Ty.Fn.t * Ctxt.Ty_param.t * Dir.t) Effect.t
  | Log_enter_tuple : (Prov.t * Ty.Tuple.t) enter -> (Prov.t * Ty.Tuple.t * Ctxt.Ty_param.t * Dir.t) Effect.t
  | Log_enter_ctor : (Prov.t * Ty.Ctor.t) enter -> (Prov.t * Ty.Ctor.t * Ctxt.Ty_param.t * Dir.t) Effect.t
  | Log_enter_exists : (Prov.t * Ty.Exists.t) enter -> (Prov.t * Ty.Exists.t * Ctxt.Ty_param.t * Dir.t) Effect.t

let ask_up ~of_ ~at = Effect.perform (Ask_up { of_; at })
let ask_ctor nm = Effect.perform (Ask_ctor nm)
let log_exit_elem elem data = Effect.perform (Log_exit_elem { elem; data })
let log_exit_generic = log_exit_elem Generic
let log_exit_ty = log_exit_elem Ty
let log_exit_fn = log_exit_elem Fn
let log_exit_tuple = log_exit_elem Tuple
let log_exit_ctor = log_exit_elem Ctor
let log_exit_exists = log_exit_elem Exists
let log_exit_union = log_exit_elem Union
let log_exit_inter = log_exit_elem Inter
let log_enter_delta delta = Effect.perform (Log_enter_delta delta)
let log_exit_delta delta = Effect.perform (Log_exit_delta delta)
let log_enter_cont_delta cont_delta = Effect.perform (Log_enter_cont_delta cont_delta)
let log_enter_ty ty ty_params dir = Effect.perform (Log_enter_ty { elem = ty; ty_params; dir })
let log_exit_cont_delta cont_delta = Effect.perform (Log_exit_cont_delta cont_delta)
let log_enter_generic prov name ty_params dir = Effect.perform (Log_enter_generic { elem = prov, name; ty_params; dir })
let log_enter_union prov tys ty_params dir = Effect.perform (Log_enter_union { elem = prov, tys; ty_params; dir })
let log_enter_inter prov tys ty_params dir = Effect.perform (Log_enter_inter { elem = prov, tys; ty_params; dir })
let log_enter_fn prov fn ty_params dir = Effect.perform (Log_enter_fn { elem = prov, fn; ty_params; dir })
let log_enter_tuple prov tuple ty_params dir = Effect.perform (Log_enter_tuple { elem = prov, tuple; ty_params; dir })
let log_enter_ctor prov ctor ty_params dir = Effect.perform (Log_enter_ctor { elem = prov, ctor; ty_params; dir })

let log_enter_exists prov exists ty_params dir =
  Effect.perform (Log_enter_exists { elem = prov, exists; ty_params; dir })
;;

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
          | Log_enter_delta delta -> Some (fun (k : (a, _) Effect.Deep.continuation) -> Effect.Deep.continue k delta)
          | Log_exit_delta delta -> Some (fun (k : (a, _) Effect.Deep.continuation) -> Effect.Deep.continue k delta)
          | Log_enter_cont_delta delta ->
            Some (fun (k : (a, _) Effect.Deep.continuation) -> Effect.Deep.continue k delta)
          | Log_exit_cont_delta delta ->
            Some (fun (k : (a, _) Effect.Deep.continuation) -> Effect.Deep.continue k delta)
          | Log_exit_elem { data; _ } -> Some (fun (k : (a, _) Effect.Deep.continuation) -> Effect.Deep.continue k data)
          | Log_enter_ty { elem = ty; ty_params; dir } ->
            Some (fun (k : (a, _) Effect.Deep.continuation) -> Effect.Deep.continue k (ty, ty_params, dir))
          | Log_enter_generic { elem = prov, name; ty_params; dir } ->
            Some (fun (k : (a, _) Effect.Deep.continuation) -> Effect.Deep.continue k (prov, name, ty_params, dir))
          | Log_enter_union { elem = prov, name; ty_params; dir } ->
            Some (fun (k : (a, _) Effect.Deep.continuation) -> Effect.Deep.continue k (prov, name, ty_params, dir))
          | Log_enter_inter { elem = prov, name; ty_params; dir } ->
            Some (fun (k : (a, _) Effect.Deep.continuation) -> Effect.Deep.continue k (prov, name, ty_params, dir))
          | Log_enter_fn { elem = prov, name; ty_params; dir } ->
            Some (fun (k : (a, _) Effect.Deep.continuation) -> Effect.Deep.continue k (prov, name, ty_params, dir))
          | Log_enter_tuple { elem = prov, name; ty_params; dir } ->
            Some (fun (k : (a, _) Effect.Deep.continuation) -> Effect.Deep.continue k (prov, name, ty_params, dir))
          | Log_enter_ctor { elem = prov, name; ty_params; dir } ->
            Some (fun (k : (a, _) Effect.Deep.continuation) -> Effect.Deep.continue k (prov, name, ty_params, dir))
          | Log_enter_exists { elem = prov, name; ty_params; dir } ->
            Some (fun (k : (a, _) Effect.Deep.continuation) -> Effect.Deep.continue k (prov, name, ty_params, dir))
          | _ -> None)
    ; retc = (fun res -> res)
    ; exnc = (fun exn -> raise exn)
    }
;;
