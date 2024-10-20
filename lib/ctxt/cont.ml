open Core
open Reporting

module Refinement = struct
  type t =
    { local : Local.Refinement.t
    ; this : Ty.Refinement.t option
    ; ty_param : Ty_param.Refinement.t
    }
  [@@deriving create, show]

  let empty = { this = None; local = Local.Refinement.empty; ty_param = Ty_param.Refinement.empty }
  let param_rfmnt { ty_param; _ } nm = Ty_param.Refinement.find ty_param nm
end

(** The per-continuation context *)
type t =
  { local : Local.t (** Local variables bound in this continuation *)
  ; ty_param : Ty_param.t (** Type parameters bound in this continuation via unpacked existentials *)
  ; is_refinements : Refinement.t list (** The stack of refinements corresponding to successive type tests, if any *)
  ; as_refinement_opt : Refinement.t option (** The refinement corresponding to type assertion, if any *)
  }
[@@deriving create, show]

(* ~~ Locals ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)

(* ~~ Type parameters ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)

(** The type parameter refinements in the current continuation are the combination of those coming from a type
    assertion (`as`) and those coming from type tests (`is`). We can have at most one `as` refinement (subsequent
    assertions refine the existing one and never go out of scope) and possibly many `is` refinements corresponding
    to nested continuation scopes. It's possible to have `is` assignments without an `as`. *)
let ty_param_refinement_opt { as_refinement_opt; is_refinements; _ } nm =
  let rec aux acc res =
    match res with
    | Ty_param.Refinement.Bounds_top :: rest -> aux acc rest
    | Ty_param.Refinement.Bounds_bottom :: _ -> Some (Ty.Param_bounds.bottom Prov.empty)
    | Ty_param.Refinement.Bounds bounds :: rest ->
      let acc = Option.value_map ~default:bounds ~f:(fun acc -> Ty.Param_bounds.meet acc bounds ~prov:Prov.empty) acc in
      aux (Some acc) rest
    | [] -> acc
  in
  let as_rfmt_opt, is_rmfts =
    Refinement.(
      ( Option.map as_refinement_opt ~f:(fun as_rfmnt -> param_rfmnt as_rfmnt nm)
      , List.map is_refinements ~f:(fun is_rfmnt -> param_rfmnt is_rfmnt nm) ))
  in
  aux None @@ Option.value_map as_rfmt_opt ~default:is_rmfts ~f:(fun as_rfmt -> as_rfmt :: is_rmfts)
;;

(** The bounds for a type parameter including all refinements *)
let ty_param_bounds ({ ty_param; _ } as t) nm =
  Option.map ~f:(fun param_bounds ->
    Option.value_map ~default:param_bounds ~f:(fun param_refinement ->
      Ty.Param_bounds.meet param_bounds param_refinement ~prov:Prov.empty)
    @@ ty_param_refinement_opt t nm)
  @@ Ty_param.find ty_param nm
;;

let bind_ty_param ty_param Ty.Param.{ name = Located.{ elem; _ }; param_bounds } =
  Ty_param.bind ty_param elem param_bounds
;;

let bind_ty_params ({ ty_param; _ } as t) ty_params =
  let ty_param = List.fold_left ty_params ~init:ty_param ~f:bind_ty_param in
  { t with ty_param }
;;
