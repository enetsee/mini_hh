open Reporting

type t =
  | Fn of Fn_def.t Located.t
  | Classish of Classish_def.t Located.t
  | Ty of Ty_def.t Located.t
[@@deriving compare, eq, sexp, show, variants]

let elab_to_generic t ~bound_ty_params =
  match t with
  | Fn fn_def ->
    Fn (Located.map (Fn_def.elab_to_generic ~bound_ty_params) fn_def)
  | Classish classish_def ->
    Classish
      (Located.map (Classish_def.elab_to_generic ~bound_ty_params) classish_def)
  | Ty ty_def ->
    Ty (Located.map (Ty_def.elab_to_generic ~bound_ty_params) ty_def)
;;
