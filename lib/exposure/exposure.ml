open Core
open Common
open Lang
module Err = Err
module Eff = Eff
module Dir = Dir

exception Exposure of Err.t list

(* ~~ Helpers to sequence result with the error as a monoid ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)

let collect_list ress =
  let rec aux ress ~k =
    match ress with
    | [] -> k ([], [])
    | next :: rest ->
      aux rest ~k:(fun (oks, errs) ->
        let acc =
          match next with
          | Ok ok -> ok :: oks, errs
          | Error err -> oks, err :: errs
        in
        k acc)
  in
  aux ress ~k:(function
    | oks, [] -> Ok oks
    | _, errs -> Error (Err.Set.union_list errs))
;;

let collect_tuple2 (res1, res2) =
  match res1, res2 with
  | Ok fst, Ok snd -> Ok (fst, snd)
  | Error err1, Error err2 -> Error (Set.union err1 err2)
  | Error err, _ | _, Error err -> Error err
;;

let collect_tuple3 (res1, res2, res3) =
  match res1, res2, res3 with
  | Ok fst, Ok snd, Ok thrd -> Ok (fst, snd, thrd)
  | Error err1, Error err2, Error err3 ->
    Error (Err.Set.union_list [ err1; err2; err3 ])
  | Error err1, Error err2, _
  | Error err1, _, Error err2
  | _, Error err1, Error err2 -> Error (Set.union err1 err2)
  | Error err, _, _ | _, Error err, _ | _, _, Error err -> Error err
;;

(* ~~ Implementation  ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
let promote_generic prov name ty_params ~dir =
  let prov, name, ty_params, dir =
    Eff.log_enter_generic prov name ty_params dir
  in
  Eff.log_exit_generic
  @@
  match Ctxt.Ty_param.find ty_params name, dir with
  | None, _ -> Error Err.(Set.singleton @@ unbound_ty_param name prov)
  | Some Ty.Param_bounds.{ upper; _ }, Dir.Up -> Ok upper
  | Some Ty.Param_bounds.{ lower; _ }, Dir.Down -> Ok lower
;;

let rec promote_ty ty ty_params ~dir =
  let ty, ty_params, dir = Eff.log_enter_ty ty ty_params dir in
  let Ty.{ node; prov } = ty in
  Eff.log_exit_ty
  @@
  let open Ty.Node in
  match node with
  | Var _ | Base _ | Nonnull -> Ok ty
  | Generic generic ->
    (* TODO(mjt) is this right? *)
    promote_generic prov generic ty_params ~dir
  | Apply apply -> promote_apply prov apply ty_params ~dir
  | Fn fn -> promote_fn prov fn ty_params ~dir
  | Tuple tuple -> promote_tuple prov tuple ty_params ~dir
  | Shape shape -> promote_shape prov shape ty_params ~dir
  | Ctor ctor -> promote_ctor prov ctor ty_params ~dir
  | Exists exists -> promote_exists prov exists ty_params ~dir
  | Forall forall -> promote_forall prov forall ty_params ~dir
  | Union union -> promote_union prov union ty_params ~dir
  | Inter inter -> promote_inter prov inter ty_params ~dir

and promote_tys tys ty_params ~dir =
  collect_list @@ List.map tys ~f:(fun ty -> promote_ty ty ty_params ~dir)

and promote_shape_field_label_map tys_map ty_params ~dir =
  Result.map ~f:Ty.Shape_field_label.Map.of_alist_exn
  @@ collect_list
  @@ List.map (Map.to_alist tys_map) ~f:(fun (key, ty) ->
    Result.map ~f:(fun ty -> key, ty) @@ promote_ty ty ty_params ~dir)

and promote_ty_opt ty_opt ty_params ~dir =
  Option.value_map ty_opt ~default:(Ok None) ~f:(fun ty ->
    Result.map ~f:(fun ty -> Some ty) @@ promote_ty ty ty_params ~dir)

and promote_union prov tys ty_params ~dir =
  let prov, tys, ty_params, dir = Eff.log_enter_union prov tys ty_params dir in
  Eff.log_exit_union
  @@ Result.map ~f:(fun elems -> Ty.union ~prov elems)
  @@ promote_tys tys ty_params ~dir

and promote_inter prov tys ty_params ~dir =
  let prov, tys, ty_params, dir = Eff.log_enter_inter prov tys ty_params dir in
  Eff.log_exit_inter
  @@ Result.map ~f:(fun elems -> Ty.inter ~prov elems)
  @@ promote_tys tys ty_params ~dir

and promote_fn prov fn ty_params ~dir =
  let prov, Ty.Fn.{ params; return }, ty_params, dir =
    Eff.log_enter_fn prov fn ty_params dir
  in
  Eff.log_exit_fn
  @@ Result.map ~f:(fun (params, return) ->
    let fn = Ty.Fn.create ~params ~return () in
    let node = Ty.Node.Fn fn in
    Ty.create ~node ~prov ())
  @@ collect_tuple2
       ( promote_tuple_help params ty_params ~dir:(Dir.flip dir)
       , promote_ty return ty_params ~dir )

and promote_tuple prov tuple ty_params ~dir =
  let prov, tuple, ty_params, dir =
    Eff.log_enter_tuple prov tuple ty_params dir
  in
  Eff.log_exit_tuple
  @@ Result.map ~f:(fun tuple ->
    let node = Ty.Node.Tuple tuple in
    Ty.create ~prov ~node ())
  @@ promote_tuple_help tuple ty_params ~dir

and promote_tuple_help Ty.Tuple.{ required; optional; variadic } ty_params ~dir =
  Result.map ~f:(fun (required, optional, variadic) ->
    Ty.Tuple.{ required; optional; variadic })
  @@ collect_tuple3
       ( promote_tys required ty_params ~dir
       , promote_tys optional ty_params ~dir
       , promote_ty_opt variadic ty_params ~dir )

and promote_shape prov Ty.Shape.{ required; optional; variadic } ty_params ~dir =
  Result.map ~f:(fun (required, optional, variadic) ->
    let shape = Ty.Shape.{ required; optional; variadic } in
    let node = Ty.Node.Shape shape in
    Ty.create ~prov ~node ())
  @@ collect_tuple3
       ( promote_shape_field_label_map required ty_params ~dir
       , promote_shape_field_label_map optional ty_params ~dir
       , promote_ty_opt variadic ty_params ~dir )

and promote_ctor prov ctor ty_params ~dir =
  let prov, Ty.Ctor.{ name; args }, ty_params, dir =
    Eff.log_enter_ctor prov ctor ty_params dir
  in
  Eff.log_exit_ctor
  @@
  match Eff.ask_ctor name with
  | Some (params, supers) ->
    let invariant_params =
      List.filter_map params ~f:(fun Ty_param_def.{ name; variance; _ } ->
        if Variance.is_inv variance.elem then Some name.elem else None)
    in
    if List.is_empty invariant_params
    then
      (* There are no invariant type parameters we can promote / demote each argument *)
      Result.map ~f:(fun args -> Ty.ctor prov ~name ~args)
      @@ collect_list
      @@ List.map2_exn args params ~f:(fun ty Ty_param_def.{ variance; _ } ->
        match variance.elem with
        | Variance.Inv -> failwith "impossible"
        | Variance.Cov -> promote_ty ty ty_params ~dir
        | Variance.Contrav -> promote_ty ty ty_params ~dir:(Dir.flip dir))
    else if Dir.is_up dir
    then
      (* We have at least one invariant parameter so there is no least supertype at the current class. Find the current
         class at each supertype, promote and take the intersection. If there are no supertypes, or no supertypes
         not containing invariant type parameters, we end up with mixed / nothing depending on the direction we're
         going in *)
      Result.map ~f:(fun supers -> Ty.inter ~prov supers)
      @@ collect_list
      @@ List.map ~f:(fun ctor -> promote_ctor prov ctor ty_params ~dir)
      @@ List.filter_map ~f:(fun at ->
        match Eff.ask_up ~of_:ctor ~at with
        | Direct args | Transitive args -> Some Ty.Ctor.{ name = at; args }
        | Not_a_subclass -> None)
      @@ Map.keys supers
    else
      (* We need to find the greatest subtype of the constructor; this requires us to find all classes which
         extend or implement this constructor. For now just return nothing *)
      Ok Ty.(nothing prov)
  | _ -> Error Err.(Set.singleton @@ unbound_ctor name prov)

and promote_exists prov exists ty_params ~dir =
  (* We don't need to worry about the quantifiers here since we won't be promoting them in the body
     TODO(mjt) -does this make sense? *)
  let prov, Ty.Exists.{ body; quants }, ty_params, dir =
    Eff.log_enter_exists prov exists ty_params dir
  in
  Eff.log_exit_exists
  @@ Result.map ~f:(fun body ->
    let exists = Ty.Exists.create ~quants ~body () in
    let node = Ty.Node.Exists exists in
    Ty.{ prov; node })
  @@ promote_ty body ty_params ~dir

and promote_forall prov forall ty_params ~dir =
  (* As above , we don't need to worry about the quantifiers here since we won't be promoting them in the body
     TODO(mjt) -does this make sense? *)
  let prov, Ty.Forall.{ body; quants }, ty_params, dir =
    prov, forall, ty_params, dir
  in
  Result.map ~f:(fun body ->
    let forall = Ty.Forall.create ~quants ~body () in
    let node = Ty.Node.Forall forall in
    Ty.{ prov; node })
  @@ promote_ty body ty_params ~dir

and promote_apply prov apply ty_params ~dir =
  let Ty.Apply.{ ty; args } = apply in
  Result.map ~f:(fun (args, ty) ->
    let apply = Ty.Apply.create ~ty ~args () in
    let node = Ty.Node.Apply apply in
    Ty.create ~node ~prov ())
  @@ collect_tuple2
       (promote_tys args ty_params ~dir, promote_ty ty ty_params ~dir)
;;

(* ~~ API ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)

let promote ty ty_params =
  Result.map_error ~f:Set.to_list @@ promote_ty ty ty_params ~dir:Up
;;

let promote_exn ty ty_params =
  match promote ty ty_params with
  | Ok ty -> ty
  | Error errs -> raise (Exposure errs)
;;

(** Demote a type [ty] by finding its greatest subtype not containing any type parameter mentioned in [ty_params] *)
let demote ty ty_params = promote_ty ty ty_params ~dir:Down

let demote_exn ty ty_params =
  match demote ty ty_params with
  | Ok ty -> ty
  | Error err -> raise (Exposure (Set.to_list err))
;;

let promote_cont_delta delta =
  let Ctxt.Cont.Delta.({ bindings; _ } as delta) =
    Eff.log_enter_cont_delta delta
  in
  let local, ty_param =
    match bindings with
    | Some Ctxt.Cont.Bindings.{ local; ty_param } -> Some local, Some ty_param
    | _ -> None, None
  in
  Eff.log_exit_cont_delta
  @@ Option.value ~default:delta
  @@ Option.map2 local ty_param ~f:(fun local ty_param ->
    let local =
      Ctxt.Local.transform local ~f:(fun ty -> promote_exn ty ty_param)
    in
    let bindings =
      Ctxt.Cont.Bindings.create ~local ~ty_param:Ctxt.Ty_param.empty ()
    in
    Ctxt.Cont.Delta.create ~bindings ())
;;

let promote_delta delta =
  let delta = Eff.log_enter_delta delta in
  Eff.log_exit_delta @@ Ctxt.Delta.lift delta ~f:promote_cont_delta
;;
