open Reporting

type t =
  { name : Name.Ty_param.t Located.t
  ; bounds : Ty.Param_bounds.t
  }
[@@deriving compare, eq, sexp, show, create]

let create_equal name ty = create ~name ~bounds:(Ty.Param_bounds.create_equal ty) ()
