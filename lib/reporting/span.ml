type t =
  { start_ : Pos.t
  ; end_ : Pos.t
  }
[@@deriving compare, create, equal, fields, sexp, show, yojson]

let empty = { start_ = Pos.empty; end_ = Pos.empty }
