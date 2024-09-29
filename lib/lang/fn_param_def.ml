open Reporting

type t =
  { ty : Ty.t
  ; name : Name.Tm_var.t Located.t
  }
[@@deriving compare, create, equal, sexp, show]
