open Core
open Common
open Reporting

type t =
  { visibility : Visibility.t Located.t
  ; static_or_instance : Static_or_instance.t
  ; name : Name.Fn.t Located.t
  ; ty : Ty.t
  ; default_value : Expr_stmt.Expr.t option
  }
[@@deriving compare, create, eq, sexp, show]
