open Core

type t =
  | Err
  | Disj of t list
  | Conj of t list
  | Multiple of t list
[@@deriving compare, eq, sexp, show, variants]
