type 'a t =
  { elem : 'a
  ; loc : Loc.t
  }
[@@deriving compare, create, eq, sexp, show]
