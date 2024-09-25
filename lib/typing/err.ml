type t =
  | Subtyping of Subtyping.Err.t
  | Alread_bound of Name.Tm_var.t
  | Unbound_local of Name.Tm_var.t
  | Unbound_at_join of Name.Tm_var.t
[@@deriving compare, eq, sexp, show, variants]
