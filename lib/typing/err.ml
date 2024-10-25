open Core
open Reporting

type t =
  | Subtyping of Subtyping.Err.t
  | Alread_bound of Name.Tm_var.t
  | Unbound_local of Name.Tm_var.t Located.t
  | Unbound_at_join of
      { bound : Name.Tm_var.t Located.t
      ; unbound : Span.t
      }
  | Unpack_arity of
      { span : Span.t
      ; n_quants : int
      ; n_names : int
      }
[@@deriving compare, eq, sexp, show, variants]
