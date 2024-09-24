open Core

(** Represents the refinement to the bounds of a type parameter occuring in the type parameter context
    Any type parameter which is bound in that context but doesn't explicitly appear in the refinement context
    has an implicit refinement of [nothing] and [mixed] *)
type t =
  | Top (** The top element:
            meet top t = meet t top = t
            join top _ = join _ top = top *)
  | Bounds of Ty.Param_bounds.t Name.Ty_param.Map.t
  | Bottom (** The bottom element:
               meet bottom _ = meet _ bottom = bottom
               join bottom t = join t bottom = t *)
[@@deriving compare, eq, sexp, variants]

let pp ppf = function
  | Top -> Fmt.any "T" ppf ()
  | Bottom -> Fmt.any "F" ppf ()
  | Bounds b -> Name.Ty_param.Map.pp Ty.Param_bounds.pp ppf b
;;

let show = Fmt.to_to_string
let empty = top
let is_empty t = Map.is_empty t

let map t ~f =
  match t with
  | Top -> Top
  | Bottom -> Bottom
  | Bounds m -> bounds @@ Name.Ty_param.Map.map m ~f
;;

let singleton generic param_bounds = bounds @@ Name.Ty_param.Map.singleton generic param_bounds

(** meet / greatest lower bound / intersection *)
let meet t1 t2 ~prov =
  match t1, t2 with
  | Top, t | t, Top -> t
  | Bottom, _ | _, Bottom -> Bottom
  | Bounds b1, Bounds b2 ->
    let f ~key:_ = function
      | `Left bounds | `Right bounds ->
        (* If the bounds are missing in the left (resp. right) refinement then they are implicitly top so
           the meet is the bounds in the right (resp. left) refinement *)
        Some bounds
      | `Both (bounds_l, bounds_r) -> Some (Ty.Param_bounds.meet bounds_l bounds_r ~prov)
    in
    Bounds (Map.merge b1 b2 ~f)
;;

let meet_many ts ~prov = List.fold_left ts ~init:top ~f:(meet ~prov)

(** join / least upper bound  / union *)
let join t1 t2 ~prov =
  match t1, t2 with
  | Top, _ | _, Top -> Top
  | Bottom, t | t, Bottom -> t
  | Bounds b1, Bounds b2 ->
    let f ~key:_ = function
      | `Left _ | `Right _ ->
        (* If the bounds are missing in the left (resp. right) refinement they are implicitly top so the join
           so the union is also top which is encoded as [None] *)
        None
      | `Both (bounds_l, bounds_r) -> Some (Ty.Param_bounds.join bounds_l bounds_r ~prov)
    in
    Bounds (Map.merge b1 b2 ~f)
;;

let join_many ts ~prov = List.fold_left ts ~init:bottom ~f:(join ~prov)

type result =
  | Bounds_top
  | Bounds_bottom
  | Bounds of Ty.Param_bounds.t

let find t name =
  match t with
  | Top -> Bounds_top
  | Bottom -> Bounds_bottom
  | Bounds m -> Option.value_map ~f:(fun b -> Bounds b) ~default:Bounds_top @@ Map.find m name
;;

let unbind t generic =
  match t with
  | Top | Bottom -> t
  | Bounds bounds -> Bounds (Map.remove bounds generic)
;;

let unbind_all t generics = List.fold_left generics ~init:t ~f:unbind
