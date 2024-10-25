open Common
open Reporting

type t =
  { visibility : Visibility.t Located.t
  ; static_or_instance : Static_or_instance.t
  ; fn_def : Fn_def.t (* ; where_constraints *)
  }
[@@deriving compare, create, eq, sexp, show]
