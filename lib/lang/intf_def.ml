open Core
open Reporting

type t =
  { name : Name.Ctor.t Located.t
  ; ty_params : Ty_param_def.t Located.t list
  ; extends : Ty.Ctor.t Located.t list
  ; required_extendss : Ty.Ctor.t Located.t list
  ; properties : Property_def.t Located.t list
  ; methods : Method_def.t Located.t list
  }
[@@deriving compare, create, eq, sexp, show]
