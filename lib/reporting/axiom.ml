type t =
  | Extends
  | Upper_bound
  | Lower_bound
[@@deriving compare, eq, sexp, show, variants, yojson]
