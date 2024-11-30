open Core

let step ~ty ~args ~ctxt_cont =
  let open Ty.Node in
  match Ty.prj ty with
  | prov, Forall { quants; _ } ->
    let n_quants = List.length quants
    and n_args = List.length args in
    if n_args <> n_quants
    then Error (Err.instantiation_arity ~prov ~n_quants ~n_args)
    else (
      let props =
        List.concat
        @@ List.map2_exn
             quants
             args
             ~f:(fun Ty.Param.{ param_bounds = { upper; lower }; _ } ty ->
               [ Prop.atom @@ Cstr.is_subtype ~ty_sub:lower ~ty_super:ty
               ; Prop.atom @@ Cstr.is_subtype ~ty_sub:ty ~ty_super:upper
               ])
      in
      Ok (Prop.conj props, ctxt_cont))
  | _prov, Var var ->
    let (_ : unit) = Eff.add_instantiation var ~args in
    Ok (Prop.true_, ctxt_cont)
  | _prov, Union tys ->
    let props =
      List.map tys ~f:(fun ty ->
        Prop.atom @@ Cstr.can_instantiate_with ~ty ~args)
    in
    Ok (Prop.conj props, ctxt_cont)
  | _prov, Inter tys ->
    let props =
      List.map tys ~f:(fun ty ->
        Prop.atom @@ Cstr.can_instantiate_with ~ty ~args)
    in
    Ok (Prop.disj props, ctxt_cont)
  | ( prov
    , ( Exists _
      | Fn _
      | Apply _
      | Generic _
      | Shape _
      | Tuple _
      | Ctor _
      | Nonnull
      | Base _ ) ) -> Error (Err.cannot_instantiate prov)
;;
