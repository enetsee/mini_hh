open Core
open Reporting

type t = (Ty.t * Span.Set.t) Name.Tm_var.Map.t [@@deriving compare, eq, sexp, show]

let empty = Name.Tm_var.Map.empty
let bottom = empty
let find (t : t) local = Option.map ~f:fst @@ Map.find t local
let is_bound (t : t) local = Map.mem t local
let singleton Located.{ span; elem } ty : t = Name.Tm_var.Map.singleton elem (ty, Span.Set.singleton span)

let diff (t : t) (tl : t) (tr : t) =
  let outer = Map.key_set t in
  Map.fold_symmetric_diff
    tl
    tr
    ~data_equal:(fun _ _ -> true)
    ~init:[]
    ~f:(fun acc (k, diff) ->
      if Set.mem outer k
      then acc
      else (
        match diff with
        | `Left (span, _) -> Either.First (k, span) :: acc
        | `Right (span, _) -> Either.Second (k, span) :: acc
        | `Unequal _ -> failwith "impossible"))
;;

(** [join] of two local contexts; if the binding is present in only one of the contexts we use that binding and if its
    present in both we use the union of the type and associated spans *)
let join t1 t2 ~prov =
  let f ~key:_ = function
    | `Left (ty, spans) | `Right (ty, spans) -> Some (ty, spans)
    | `Both ((ty1, spans1), (ty2, spans2)) -> Some (Ty.union ~prov [ ty1; ty2 ], Set.union spans1 spans2)
  in
  Map.merge t1 t2 ~f
;;

(** [meet] of two local contexts; if the binding is present in only one of the contexts we drop the binding and if it's
    present in both we use the intersection of the type and associated spans *)
let meet (t1 : t) (t2 : t) ~prov =
  let f ~key:_ = function
    | `Left _ | `Right _ -> None
    | `Both ((ty1, spans1), (ty2, spans2)) -> Some (Ty.inter ~prov [ ty1; ty2 ], Set.inter spans1 spans2)
  in
  Map.merge t1 t2 ~f
;;

(** [extend]ing a local context means that we have all the bindings from both contexts but if a binding is present
    in both, we take the binding from the second one. *)
let extend t ~with_ : t =
  let f ~key:_ = function
    | `Left v | `Right v | `Both (_, v) -> Some v
  in
  Map.merge t with_ ~f
;;

let bind (t : t) Located.{ elem; span } ty : t = Map.update t elem ~f:(fun _ -> ty, Span.Set.singleton span)
let bind_all (t : t) tm_var_tys : t = List.fold_left tm_var_tys ~init:t ~f:(fun t (tm_var, ty) -> bind t tm_var ty)
let transform (t : t) ~f = Name.Tm_var.Map.map t ~f:(fun (ty, spans) -> f ty, spans)

module Refinement = struct
  (** A local refinement is a map from term variables names to formula over types*)
  type t = Ty.Refinement.t Name.Tm_var.Map.t [@@deriving compare, eq, sexp, show]

  let find (t : t) nm = Map.find t nm

  let join t1 t2 ~prov =
    let f ~key:_ elem =
      match elem with
      | `Left _ty_rfmt | `Right _ty_rfmt -> None
      | `Both (ty_rfmt1, ty_rfmt2) -> Some (Ty.Refinement.join ty_rfmt1 ty_rfmt2 ~prov)
    in
    Map.merge t1 t2 ~f
  ;;

  let meet t1 t2 ~prov =
    let f ~key:_ elem =
      match elem with
      | `Left ty_rfmt | `Right ty_rfmt -> Some ty_rfmt
      | `Both (ty_rfmt1, ty_rfmt2) -> Some (Ty.Refinement.meet ty_rfmt1 ty_rfmt2 ~prov)
    in
    Map.merge t1 t2 ~f
  ;;

  let empty = Name.Tm_var.Map.empty
  let singleton nm ty_refinement = Name.Tm_var.Map.singleton nm ty_refinement
  let invalidate t nm = Map.remove t nm
end
