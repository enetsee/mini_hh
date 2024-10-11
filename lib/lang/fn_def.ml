open Reporting

type t =
  { name : Name.Fn.t Located.t
  ; lambda : Expr_stmt.Lambda.t
  }
[@@deriving compare, create, eq, sexp, show]
