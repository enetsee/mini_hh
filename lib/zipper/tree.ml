open Core

type 'a t =
  | Leaf of 'a
  | Branch of 'a t list
[@@deriving compare, eq, map, sexp, variants]
