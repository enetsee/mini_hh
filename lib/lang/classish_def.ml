open Core
open Reporting

type t =
  { kind : Classish_kind.t Located.t
  ; name : Name.Ctor.t Located.t
  ; ty_params : Ty_param_def.t list
  ; extends : Ty.Ctor.t Located.t option
  ; implements : Ty.Ctor.t Located.t list
  ; require_class : Ty.Ctor.t Located.t list
  ; require_extends : Ty.Ctor.t Located.t list
  ; require_implements : Ty.Ctor.t Located.t list
  ; uses : Ty.Ctor.t Located.t list
  ; ty_consts : Ty_const_def.t Located.t list
  ; properties : Property_def.t Located.t list
  ; methods : Method_def.t Located.t list
  }
[@@deriving compare, create, eq, sexp, show]

let ty_of { name; ty_params; _ } =
  let args =
    List.map ty_params ~f:(fun Ty_param_def.{ name; _ } ->
      let prov = Prov.witness @@ Located.span_of name in
      let name = Located.elem name in
      Ty.generic prov name)
  in
  let prov = Prov.witness @@ Located.span_of name in
  let name = Located.elem name in
  Ty.ctor prov ~name ~args
;;
