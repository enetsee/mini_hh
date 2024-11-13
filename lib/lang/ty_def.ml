open Core
open Reporting

module Kind = struct
  type t =
    | Case
    | New
    | Alias
  [@@deriving eq, compare, sexp, show, variants]

  let to_string = function
    | Case -> "case type"
    | New -> "newtype"
    | Alias -> "type"
  ;;
end

type t =
  { kind : Kind.t Located.t
  ; name : Name.Ctor.t Located.t
  ; ty_params : Ty_param_def.t list
  ; bounds : Ty.Param_bounds.t
  ; defs : (Ty.t * Ty.Param.t list) list
  }
[@@deriving compare, create, eq, sexp, show]

let elab_to_generic t ~bound_ty_params:_ = t
