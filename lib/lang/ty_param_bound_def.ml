type t =
  | As of Ty.t
  | Super of Ty.t
[@@deriving compare, eq, sexp, show, variants]
