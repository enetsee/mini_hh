open Reporting
open Common

type t =
  { name : Name.Ty_param.t Located.t
  ; variance : Variance.t Located.t
  ; param_bounds : Ty.Param_bounds.t
  }
[@@deriving compare, create, eq, sexp, show]

let to_ty_param { name; param_bounds; _ } =
  Ty.Param.create ~name ~param_bounds ()
;;

let elab_to_generic t ~bound_ty_params =
  let param_bounds =
    Ty.Param_bounds.elab_to_generic t.param_bounds ~bound_ty_params
  in
  { t with param_bounds }
;;
