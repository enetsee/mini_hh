type t =
  | Inv
  | Cov
  | Contrav
[@@deriving compare, equal, sexp, show, variants]

let meet t1 t2 =
  match t1, t2 with
  | Inv, _ | _, Inv | Cov, Contrav | Contrav, Cov -> Inv
  | Cov, Cov -> Cov
  | Contrav, Contrav -> t1
;;
