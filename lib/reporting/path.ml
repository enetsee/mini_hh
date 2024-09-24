open Core

type t = string list [@@deriving compare, eq, sexp, show, yojson]

let empty = []
