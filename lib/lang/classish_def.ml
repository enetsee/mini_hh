open Core
open Reporting

type t =
  { kind : Classish_kind.t Located.t
  ; name : Name.Ctor.t Located.t
  ; ty_params : Ty_param_def.t list
  ; extends : Ty.Ctor.t Located.t option
  ; implements : Ty.Ctor.t Located.t list
  ; require_extends : Ty.Ctor.t Located.t list
  ; require_implements : Ty.Ctor.t Located.t list
  ; uses : Ty.Ctor.t Located.t list
  ; ty_consts : Ty_const_def.t Located.t list
  ; properties : Property_def.t Located.t list
  ; methods : Method_def.t Located.t list
  }
[@@deriving compare, create, eq, sexp, show]
