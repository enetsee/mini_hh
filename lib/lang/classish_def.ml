open Core
open Reporting

module Kind = struct
  type t =
    | Class of
        { is_abstract : Span.t option
        ; is_final : Span.t option
        }
    | Intf
    | Trait
  [@@deriving eq, compare, sexp, show, variants]

  let to_string = function
    | Class { is_abstract = None; is_final = None } -> "class"
    | Class { is_abstract = _; is_final = None } -> "abstract class"
    | Class { is_abstract = None; is_final = _ } -> "final class"
    | Class { is_abstract = _; is_final = _ } -> "abstract final class"
    | Intf -> "interface"
    | Trait -> "trait"
  ;;
end

type t =
  { kind : Kind.t Located.t
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

let elab_to_generic t ~bound_ty_params =
  (* Bind class level generics *)
  let bound_ty_params =
    let declared_ty_params =
      Name.Ty_param.Set.of_list
      @@ List.map
           ~f:(fun Ty_param_def.{ name; _ } -> Located.elem name)
           t.ty_params
    in
    Set.union bound_ty_params declared_ty_params
  in
  let f = Located.map (Ty.Ctor.elab_to_generic ~bound_ty_params) in
  (* We need to elaborate the type parameters since the declared type parameters may appear in other type paramerter
     bounds *)
  let ty_params =
    List.map ~f:(Ty_param_def.elab_to_generic ~bound_ty_params) t.ty_params
  and extends = Option.map ~f t.extends
  and implements = List.map ~f t.implements
  and require_class = List.map ~f t.require_class
  and require_extends = List.map ~f t.require_extends
  and require_implements = List.map ~f t.require_implements
  and uses = List.map ~f t.uses
  and ty_consts =
    List.map
      ~f:(Located.map (Ty_const_def.elab_to_generic ~bound_ty_params))
      t.ty_consts
  and properties =
    List.map
      ~f:(Located.map (Property_def.elab_to_generic ~bound_ty_params))
      t.properties
  and methods =
    List.map
      ~f:(Located.map (Method_def.elab_to_generic ~bound_ty_params))
      t.methods
  in
  { t with
    ty_params
  ; extends
  ; implements
  ; require_class
  ; require_extends
  ; require_implements
  ; uses
  ; ty_consts
  ; properties
  ; methods
  }
;;
