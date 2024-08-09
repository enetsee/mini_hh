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
let promote_generic generic ty_params ~dir =
  match Envir.Ty_param.find ty_params generic, dir with
  | None, _ -> Ok (Ty.Generic generic)
  | Some Ty.Param_bounds.{ upper_bound; _ }, Up -> Ok (Option.value ~default:Ty.mixed upper_bound)
  | Some Ty.Param_bounds.{ lower_bound; _ }, Down -> Ok (Option.value ~default:Ty.nothing lower_bound)
;;

let rec promote_help ty ty_params ~dir ~oracle =
  match ty with
  | Ty.Base _ -> Ok ty
  | Ty.Generic generic -> promote_generic generic ty_params ~dir
  | Ty.Fn fn -> promote_fn fn ty_params ~dir ~oracle
  | Ty.Ctor ctor -> promote_ctor ctor ty_params ~dir ~oracle
  | Ty.Exists exists -> promote_exists exists ty_params ~dir ~oracle
  | Ty.Union union -> Result.map ~f:(fun union -> Ty.Union union) @@ promotes union ty_params ~dir ~oracle
  | Ty.Inter inter -> Result.map ~f:(fun inter -> Ty.Inter inter) @@ promotes inter ty_params ~dir ~oracle

and promotes tys ty_params ~dir ~oracle =
  collect_list @@ List.map tys ~f:(fun ty -> promote_help ty ty_params ~dir ~oracle)

and promote_opt ty_opt ty_params ~dir ~oracle =
  match ty_opt with
  | None -> Ok None
  | Some ty -> Result.map ~f:(fun ty -> Some ty) @@ promote_help ty ty_params ~dir ~oracle

and promote_fn Ty.Fn.{ params; return } ty_params ~dir ~oracle =
  Result.map ~f:(fun (params, return) -> Ty.Fn Ty.Fn.{ params; return })
  @@ collect_tuple2
       (promote_fn_params params ty_params ~dir:(flip dir) ~oracle, promote_help return ty_params ~dir ~oracle)

and promote_fn_params Ty.Fn_params.{ required; optional; variadic } ty_params ~dir ~oracle =
  Result.map ~f:(fun (required, optional, variadic) -> Ty.Fn_params.{ required; optional; variadic })
  @@ collect_tuple3
       ( promotes required ty_params ~dir ~oracle
       , promotes optional ty_params ~dir ~oracle
       , promote_opt variadic ty_params ~dir ~oracle )

and promote_ctor ctor ty_params ~dir ~oracle =
  let Ty.Ctor.{ ctor = id; args } = ctor in
  match Oracle.find_ctor oracle id with
  | Some (params, supers) ->
    let invariant_params =
      List.filter_map params ~f:(fun (id, var, _) -> if Variance.is_inv var then Some id else None)
    in
    if List.is_empty invariant_params
    then
      (* There are no invariant type parameters we can promote / demote each argument *)
      Result.map ~f:(fun args -> Ty.ctor id args)
      @@ collect_list
      @@ List.map2_exn args params ~f:(fun ty (_, var, _) ->
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
      Result.map ~f:(fun supers -> Ty.inter supers)
      @@ collect_list
      @@ List.map ~f:(fun ctor -> promote_ctor ctor ty_params ~dir ~oracle)
      @@ List.filter_map ~f:(fun at ->
        Option.map ~f:(fun (args, _) -> Ty.Ctor.{ ctor = at; args }) @@ Oracle.up oracle ~of_:ctor ~at)
      @@ Map.keys supers
    else
      (* We need to find the greatest subtype of the constructor; this requires us to find all classes which
         extend or implement this constructor. For now just return nothing *)
      Ok Ty.nothing
  | _ -> Error Err.(Set.singleton @@ unbound_ctor id)

and promote_exists exists ty_params ~dir ~oracle =
  (* We don't need to worry about the quantifiers here since we won't be promoting them in the body
     TODO(mjt) -does this make sense? *)
  let Ty.Exists.{ body; quants } = exists in
  Result.map ~f:(fun body -> Ty.exists quants body) @@ promote_help body ty_params ~dir ~oracle
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
