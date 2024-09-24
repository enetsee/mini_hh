open Core
open Common
module Err = Err

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
  | Error err1, Error err2, Error err3 -> Error (Err.Set.union_list [ err1; err2; err3 ])
  | Error err1, Error err2, _ | Error err1, _, Error err2 | _, Error err1, Error err2 -> Error (Set.union err1 err2)
  | Error err, _, _ | _, Error err, _ | _, _, Error err -> Error err
;;

(* ~~ Record the direction  (promotion / demotion) ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
type dir =
  | Up
  | Down

let flip = function
  | Up -> Down
  | Down -> Up
;;

let is_up = function
  | Up -> true
  | _ -> false
;;

(* ~~ Implementation  ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
let promote_generic (prov, generic) ty_params ~dir =
  match Envir.Ty_param.find ty_params generic, dir with
  | None, _ -> Ok (Ty.generic prov generic)
  | Some Ty.Param_bounds.{ upper; _ }, Up -> Ok upper
  | Some Ty.Param_bounds.{ lower; _ }, Down -> Ok lower
;;

let rec promote_help ty ty_params ~dir ~oracle =
  let Ty.{ node; prov } = ty in
  match node with
  | Ty.Node.Base _ -> Ok ty
  | Ty.Node.Generic generic -> promote_generic (prov, generic) ty_params ~dir
  | Ty.Node.Fn fn ->
    Result.map ~f:(fun fn ->
      let node = Ty.Node.Fn fn in
      Ty.{ prov; node })
    @@ promote_fn fn ty_params ~dir ~oracle
  | Ty.Node.Tuple tuple ->
    Result.map ~f:(fun tuple ->
      let node = Ty.Node.Tuple tuple in
      Ty.{ prov; node })
    @@ promote_tuple tuple ty_params ~dir ~oracle
  | Ty.Node.Ctor ctor -> promote_ctor (prov, ctor) ty_params ~dir ~oracle
  | Ty.Node.Exists exists ->
    Result.map ~f:(fun exists ->
      let node = Ty.Node.Exists exists in
      Ty.{ prov; node })
    @@ promote_exists exists ty_params ~dir ~oracle
  | Ty.Node.Union union -> Result.map ~f:(fun elems -> Ty.union ~prov elems) @@ promotes union ty_params ~dir ~oracle
  | Ty.Node.Inter inter -> Result.map ~f:(fun elems -> Ty.inter ~prov elems) @@ promotes inter ty_params ~dir ~oracle

and promotes tys ty_params ~dir ~oracle =
  collect_list @@ List.map tys ~f:(fun ty -> promote_help ty ty_params ~dir ~oracle)

and promote_opt ty_opt ty_params ~dir ~oracle =
  match ty_opt with
  | None -> Ok None
  | Some ty -> Result.map ~f:(fun ty -> Some ty) @@ promote_help ty ty_params ~dir ~oracle

and promote_fn Ty.Fn.{ params; return } ty_params ~dir ~oracle =
  Result.map ~f:(fun (params, return) -> Ty.Fn.{ params; return })
  @@ collect_tuple2 (promote_tuple params ty_params ~dir:(flip dir) ~oracle, promote_help return ty_params ~dir ~oracle)

and promote_tuple Ty.Tuple.{ required; optional; variadic } ty_params ~dir ~oracle =
  Result.map ~f:(fun (required, optional, variadic) -> Ty.Tuple.{ required; optional; variadic })
  @@ collect_tuple3
       ( promotes required ty_params ~dir ~oracle
       , promotes optional ty_params ~dir ~oracle
       , promote_opt variadic ty_params ~dir ~oracle )

and promote_ctor (prov, ctor) ty_params ~dir ~oracle =
  let Ty.Ctor.{ name; args } = ctor in
  match Oracle.find_ctor oracle name with
  | Some (params, supers) ->
    let invariant_params =
      List.filter_map params ~f:(fun (id, var, _, _) -> if Variance.is_inv var then Some id else None)
    in
    if List.is_empty invariant_params
    then
      (* There are no invariant type parameters we can promote / demote each argument *)
      Result.map ~f:(fun args -> Ty.ctor prov ~name ~args)
      @@ collect_list
      @@ List.map2_exn args params ~f:(fun ty (_, var, _, _) ->
        match var with
        | Variance.Inv -> failwith "impossible"
        | Variance.Cov -> promote_help ty ty_params ~dir ~oracle
        | Variance.Contrav -> promote_help ty ty_params ~dir:(flip dir) ~oracle)
    else if is_up dir
    then
      (* We have at least one invariant parameter so there is no least supertype at the current class. Find the current
         class at each supertype, promote and take the intersection. If there are no supertypes, or no supertypes
         not containing invariant type parameters, we end up with mixed / nothing depending on the direction we're
         going in *)
      Result.map ~f:(fun supers -> Ty.inter ~prov supers)
      @@ collect_list
      @@ List.map ~f:(fun ctor -> promote_ctor (prov, ctor) ty_params ~dir ~oracle)
      @@ List.filter_map ~f:(fun at ->
        Option.map ~f:(fun args -> Ty.Ctor.{ name = at; args }) @@ Oracle.up oracle ~of_:ctor ~at)
      @@ Map.keys supers
    else
      (* We need to find the greatest subtype of the constructor; this requires us to find all classes which
         extend or implement this constructor. For now just return nothing *)
      Ok Ty.(nothing prov)
  | _ -> Error Err.(Set.singleton @@ unbound_ctor name prov)

and promote_exists exists ty_params ~dir ~oracle =
  (* We don't need to worry about the quantifiers here since we won't be promoting them in the body
     TODO(mjt) -does this make sense? *)
  let Ty.Exists.{ body; quants } = exists in
  Result.map ~f:(fun body -> Ty.Exists.create ~quants ~body ()) @@ promote_help body ty_params ~dir ~oracle
;;

(* ~~ API ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)

let promote ty ty_params ~oracle = promote_help ty ty_params ~dir:Up ~oracle

let promote_exn ty ty_params ~oracle =
  match promote ty ty_params ~oracle with
  | Ok ty -> ty
  | Error err -> raise (Exposure (Set.to_list err))
;;

(** Demote a type [ty] by finding its greatest subtype not containing any type parameter mentioned in [ty_params] *)
let demote ty ty_params ~oracle = promote_help ty ty_params ~dir:Down ~oracle

let demote_exn ty ty_params ~oracle =
  match demote ty ty_params ~oracle with
  | Ok ty -> ty
  | Error err -> raise (Exposure (Set.to_list err))
;;
