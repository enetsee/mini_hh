open Reporting

type t =
  { name : Name.Ty_param.t Located.t
  ; bounds : Ty.Param_bounds.t
  }
[@@deriving compare, eq, sexp, show, create]

let create_equal name ty = create ~name ~bounds:(Ty.Param_bounds.create_equal ty) ()

let elab_to_generic { name; bounds } ~bound_ty_params =
  let bounds = Ty.Param_bounds.elab_to_generic bounds ~bound_ty_params in
  { name; bounds }
;;
