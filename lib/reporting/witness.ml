open Core

module Def = struct
  type t = Where_clause of Span.t [@@deriving compare, eq, sexp, show, variants, yojson]
end

module Lit = struct
  type t =
    | Lnum of Span.t
    | Dnum of Span.t
    | Bool of Span.t
    | Null of Span.t
    | Const_string of Span.t
  [@@deriving compare, eq, sexp, show, variants, yojson]
end

module Lvalue = struct
  type t = Tm_var of Span.t [@@deriving compare, eq, sexp, show, variants, yojson]
end

module Expr = struct
  type t =
    | Is of Span.t
    | As of Span.t
    | If_cond of Span.t
    | Tm_var of Span.t
  [@@deriving compare, eq, sexp, show, variants, yojson]
end

module Stmt = struct
  type t = If_join of Span.t [@@deriving compare, eq, sexp, show, variants, yojson]
end

type t =
  | Lit of Lit.t
  | Expr of Expr.t
  | Stmt of Stmt.t
  | Def of Def.t
  | Lvalue of Lvalue.t
  | Witness of Span.t
  | Witnesses of Span.t list
[@@deriving compare, eq, sexp, show, variants, yojson]

let lit_null span = lit (Lit.null span)
let lit_bool span = lit (Lit.bool span)
let lit_lnum span = lit (Lit.lnum span)
let lit_dnum span = lit (Lit.dnum span)
let lit_const_string span = lit (Lit.const_string span)
let expr_is span = expr @@ Expr.is span
let expr_as span = expr @@ Expr.as_ span
let expr_if_cond span = expr @@ Expr.if_cond span
let expr_tm_var span = expr @@ Expr.tm_var span
let lvalue_tm_var span = lvalue (Lvalue.tm_var span)
let stmt_if_join span = stmt (Stmt.if_join span)
let def_where_clause span = def (Def.where_clause span)
