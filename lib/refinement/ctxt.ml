open Core
open Reporting

type t =
  { ty_param : Ty.Param.Ctxt.t
  ; ty_param_refine : Ty.Param.Refinement.t
  ; oracle : Oracle.t
  ; ty_param_source : int
  }
[@@deriving create, show]

let create = create ~ty_param_source:0

let fresh_generics ({ ty_param_source; _ } as t) n =
  let ty_param_source = ty_param_source + n in
  ( { t with ty_param_source }
  , List.init n ~f:(fun n -> Name.Ty_param.of_string @@ Format.sprintf "T#%n" (ty_param_source + n)) )
;;

let param_bounds { ty_param; ty_param_refine; _ } id =
  Option.map ~f:(fun bounds ->
    match Ty.Param.Refinement.find ty_param_refine id with
    | Ty.Param.Refinement.Bounds_top -> bounds
    | Ty.Param.Refinement.Bounds_bottom -> Ty.Param_bounds.bottom Reporting.Prov.empty
    | Ty.Param.Refinement.Bounds other -> Ty.Param_bounds.meet bounds other ~prov:Reporting.Prov.empty)
  @@ Ty.Param.Ctxt.find ty_param id
;;

let bind_param ty_param Ty.Param.{ name = Located.{ elem; _ }; param_bounds } =
  Ty.Param.Ctxt.bind ty_param elem param_bounds
;;

let bind_all ({ ty_param; _ } as t) ty_params =
  let ty_param = List.fold_left ty_params ~init:ty_param ~f:bind_param in
  { t with ty_param }
;;

let up { oracle; _ } ~of_ ~at = Oracle.up oracle ~of_ ~at
