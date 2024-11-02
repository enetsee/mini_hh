open Common
open Reporting

type t =
  { visibility : Visibility.t Located.t
  ; static_or_instance : Static_or_instance.t
  ; fn_def : Fn_def.t (* ; where_constraints *)
  }
[@@deriving compare, create, eq, sexp, show]

let elab_to_generic t ~bound_ty_params =
  let fn_def = Fn_def.elab_to_generic t.fn_def ~bound_ty_params in
  { t with fn_def }
;;
