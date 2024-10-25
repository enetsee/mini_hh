open Core
open Reporting

type t =
  { name : Name.Fn.t Located.t
  ; lambda : Expr_stmt.Lambda.t
  ; where_constraints : Ty.Param.t list
  }
[@@deriving compare, create, eq, sexp, show]
