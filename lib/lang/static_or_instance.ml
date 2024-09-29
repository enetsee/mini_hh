open Reporting

type t =
  | Static of Loc.t
  | Instance
[@@deriving compare, eq, sexp, show, variants]
