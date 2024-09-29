open Reporting

type t =
  { name : Name.Fn.t Located.t
  ; signature : Expr_stmt.Lambda_sig.t Located.t
  ; def : Expr_stmt.Lambda.t Located.t
  }
[@@deriving compare, create, eq, sexp, show]
