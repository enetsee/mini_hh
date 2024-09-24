open Core

type t =
  { path : Path.t
  ; span : Span.t
  }
[@@deriving compare, create, eq, sexp, show, yojson]

let empty = { path = Path.empty; span = Span.empty }
