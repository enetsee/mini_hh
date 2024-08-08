type t =
  | Inv
  | Cov
  | Contrav
[@@deriving compare, equal, sexp, show, variants]
