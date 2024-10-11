open Reporting

type t =
  | Static of Span.t
  | Instance
[@@deriving compare, eq, sexp, show, variants]
