open Core

type t =
  | Top
  | Bounds of Ty.Param_bounds.t Ty.Generic.Map.t
[@@deriving compare, eq, sexp, variants]

let pp ppf = function
  | Top -> Fmt.any "T" ppf ()
  | Bounds b -> Ty.Generic.Map.pp Ty.Param_bounds.pp ppf b
;;

let show = Fmt.to_to_string
let empty = Bounds Ty.Generic.Map.empty
let is_empty t = Map.is_empty t

let map t ~f =
  match t with
  | Top -> Top
  | Bounds m -> bounds @@ Ty.Generic.Map.map m ~f
;;

(** The bottom element:
    meet bottom _ = meet _ bottom = bottom
    join bottom t = join t bottom = t *)
let bottom = empty

(** The top element:
    meet top t = meet t top = t
    join top _ = join _ top = top *)
let top = Top

let meet t1 t2 =
  match t1, t2 with
  | Top, t | t, Top -> t
  | Bounds b1, Bounds b2 ->
    let f ~key:_ = function
      | `Left _ | `Right _ -> None
      | `Both (bounds_l, bounds_r) -> Some (Ty.Param_bounds.meet bounds_l bounds_r)
    in
    Bounds (Map.merge b1 b2 ~f)
;;

let join t1 t2 =
  match t1, t2 with
  | Top, _ | _, Top -> Top
  | Bounds b1, Bounds b2 ->
    let f ~key:_ = function
      | `Left bounds | `Right bounds -> Some bounds
      | `Both (bounds_l, bounds_r) -> Some (Ty.Param_bounds.join bounds_l bounds_r)
    in
    Bounds (Map.merge b1 b2 ~f)
;;

let find t id =
  match t with
  | Top -> Some Ty.Param_bounds.top
  | Bounds m -> Map.find m id
;;
