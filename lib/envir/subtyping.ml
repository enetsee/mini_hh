open Core

(** TODO(mjt) Implement inference environemnt *)
type t = unit [@@deriving compare, eq, sexp, show]

let empty = ()
