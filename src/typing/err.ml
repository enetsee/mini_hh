type t =
  | Subtyping of Subtyping.Err.t
  | Alread_bound of Lang.Local.t
  | Unbound_local of Lang.Local.t
[@@deriving compare, eq, sexp, show, variants]
