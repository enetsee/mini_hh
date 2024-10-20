open Reporting

type t =
  { name : Name.Fn.t Located.t
  ; ret_ty : Ty.t
  }
[@@deriving create, show]
