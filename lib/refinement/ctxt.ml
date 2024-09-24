open Core

type t =
  { ty_param : Envir.Ty_param.t
  ; ty_param_refine : Envir.Ty_param_refine.t
  ; oracle : Oracle.t
  }
[@@deriving create, show]

let param_bounds { ty_param; ty_param_refine; _ } id =
  Option.map ~f:(fun bounds ->
    match Envir.Ty_param_refine.find ty_param_refine id with
    | Envir.Ty_param_refine.Bounds_top -> bounds
    | Envir.Ty_param_refine.Bounds_bottom -> Ty.Param_bounds.bottom Reporting.Prov.empty
    | Envir.Ty_param_refine.Bounds other -> Ty.Param_bounds.meet bounds other ~prov:Reporting.Prov.empty)
  @@ Envir.Ty_param.find ty_param id
;;

let bind_param ty_param Ty.Param.{ name; param_bounds } = Envir.Ty_param.bind ty_param name param_bounds

let bind_all ({ ty_param; _ } as t) ty_params =
  let ty_param = List.fold_left ty_params ~init:ty_param ~f:bind_param in
  { t with ty_param }
;;

let up { oracle; _ } ~of_ ~at = Oracle.up oracle ~of_ ~at

let merge_disjoint_exn t ty_param' =
  let { ty_param; _ } = t in
  let ty_param = Envir.Ty_param.merge_disjoint_exn ty_param ty_param' in
  { t with ty_param }
;;
