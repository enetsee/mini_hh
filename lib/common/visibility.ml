type t =
  | Public
  | Private
[@@deriving compare, eq, sexp, show, variants]
