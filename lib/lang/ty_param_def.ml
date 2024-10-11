open Reporting
open Common

type t =
  { name : Name.Ty_param.t Located.t
  ; variance : Variance.t Located.t
  ; bounds : Ty.Param_bounds.t
  }
[@@deriving compare, create, eq, sexp, show]
