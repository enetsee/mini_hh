open Core
open Reporting

type param_kind =
  | Required
  | Optional
  | Variadic
[@@deriving compare, eq, sexp, variants]

module Minimal = struct
  type t =
    | Not_a_subtype of
        { ty_sub : Ty.t
        ; ty_super : Ty.t
        }
    | Tuple_arity of
        { param_kind : param_kind
        ; prov_sub : Prov.t
        ; n_sub : int
        ; prov_super : Prov.t
        ; n_super : int
        }
    | Shape_field_required_super of
        { prov_sub : Prov.t
        ; prov_super : Prov.t
        ; lbl : Ty.Shape_field_label.t
        ; optional_in_sub : bool
        }
    | Shape_field_required_sub of
        { prov_sub : Prov.t
        ; prov_super : Prov.t
        ; lbl : Ty.Shape_field_label.t
        }
    | Shape_field_optional_sub of
        { prov_sub : Prov.t
        ; prov_super : Prov.t
        ; lbl : Ty.Shape_field_label.t
        ; required_in_super : bool
        }
    | Shape_sub_open_super_closed of
        { prov_sub : Prov.t
        ; prov_super : Prov.t
        }
    | Instantiation_arity of
        { prov : Prov.t
        ; n_quants : int
        ; n_args : int
        }
    | Cannot_instantiate of Prov.t
    | Disj of t list
    | Conj of t list
    | Multiple of t list
  [@@deriving compare, eq, sexp, variants]

  let pp_param_kind ppf t =
    match t with
    | Required -> Fmt.any "required" ppf ()
    | Optional -> Fmt.any "optional" ppf ()
    | Variadic -> Fmt.any "variadic" ppf ()
  ;;

  let pp_param_plural ppf n =
    if n = 1 then Fmt.any "parameter" ppf () else Fmt.any "parameters" ppf ()
  ;;

  let pp_num_or_no ppf n = if n = 0 then Fmt.any "no" ppf () else Fmt.int ppf n

  let pp_num_or_none ppf n =
    if n = 0 then Fmt.any "none" ppf () else Fmt.int ppf n
  ;;

  let pp_arity ppf (n, param_kind) =
    Fmt.(
      pair ~sep:sp pp_num_or_no @@ pair ~sep:sp pp_param_kind pp_param_plural)
      ppf
      (n, (param_kind, n))
  ;;

  let rec pp ppf t =
    match t with
    | Not_a_subtype { ty_sub; ty_super } ->
      Fmt.(hovbox @@ pair ~sep:(any " </: ") Ty.pp Ty.pp) ppf (ty_sub, ty_super)
    | Tuple_arity { param_kind; prov_sub = _; n_sub; prov_super = _; n_super }
      ->
      Fmt.(
        hovbox
        @@ pair
             ~sep:sp
             (any "The subtype had " ++ pp_arity)
             (any "but the supertype had " ++ pp_num_or_none))
        ppf
        ((n_sub, param_kind), n_super)
    | Shape_sub_open_super_closed _ ->
      Fmt.(
        any "The subtype is an open shape but the supertype is a closed shape")
        ppf
        ()
    | Shape_field_optional_sub { lbl; required_in_super; _ } ->
      if required_in_super
      then
        Fmt.(
          any "The field "
          ++ Ty.Shape_field_label.pp
          ++ any " is optional in the subtype but required in the supertype")
          ppf
          lbl
      else
        Fmt.(
          any "The field "
          ++ Ty.Shape_field_label.pp
          ++ any " is optional in the subtype but not defined in the supertype")
          ppf
          lbl
    | Shape_field_required_super { lbl; optional_in_sub; _ } ->
      if optional_in_sub
      then
        Fmt.(
          any "The field "
          ++ Ty.Shape_field_label.pp
          ++ any " is optional in the subtype but required in the supertype")
          ppf
          lbl
      else
        Fmt.(
          any "The field "
          ++ Ty.Shape_field_label.pp
          ++ any " is required in the supertype but not defined in the subtype")
          ppf
          lbl
    | Shape_field_required_sub { lbl; _ } ->
      Fmt.(
        any "The field "
        ++ Ty.Shape_field_label.pp
        ++ any " is required in the subtype but not defined in the supertype")
        ppf
        lbl
    | Cannot_instantiate _ ->
      Fmt.(any "Only universally quantified types can be applied") ppf ()
    | Instantiation_arity { n_quants; n_args; _ } ->
      Fmt.(
        any "Arity mismatch when apply this type. It has "
        ++ pair
             ~sep:sp
             (int ++ any " quantifiers but is applied to")
             (int ++ any " types"))
        ppf
        (n_quants, n_args)
    | Disj ts -> Fmt.(hovbox @@ list ~sep:(any " | ") pp) ppf ts
    | Conj ts -> Fmt.(hovbox @@ list ~sep:(any " & ") pp) ppf ts
    | Multiple ts -> Fmt.(vbox @@ list ~sep:cut pp) ppf ts
  ;;
end

include Minimal
include Pretty.Make (Minimal)

let tuple_arity_required = tuple_arity ~param_kind:Required
let tuple_arity_optional = tuple_arity ~param_kind:Required
let tuple_arity_variadic = tuple_arity ~param_kind:Required ~n_sub:0 ~n_super:1
