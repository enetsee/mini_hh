type t =
  { pos_start : Pos.t
  ; pos_end : Pos.t
  }
[@@deriving compare, create, equal, fields, sexp, show, yojson]

let empty = { pos_start = Pos.empty; pos_end = Pos.empty }
