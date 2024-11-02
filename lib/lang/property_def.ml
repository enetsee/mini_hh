open Core
open Common
open Reporting

type t =
  { visibility : Visibility.t Located.t
  ; static_or_instance : Static_or_instance.t
  ; name : Name.Tm_var.t Located.t
  ; ty : Ty.t
  ; default_value : Expr_stmt.Expr.t option
  }
[@@deriving compare, create, eq, sexp, show]

let elab_to_generic t ~bound_ty_params =
  let ty = Ty.elab_to_generic t.ty ~bound_ty_params
  and default_value = Option.map t.default_value ~f:(Expr_stmt.Expr.elab_to_generic ~bound_ty_params) in
  { t with ty; default_value }
;;
