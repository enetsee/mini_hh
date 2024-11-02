open Reporting

type t =
  { ty : Ty.t
  ; name : Name.Tm_var.t Located.t
  }
[@@deriving compare, create, equal, sexp, show]

let elab_to_generic { ty; name } ~bound_ty_params =
  let ty = Ty.elab_to_generic ty ~bound_ty_params in
  { ty; name }
;;
