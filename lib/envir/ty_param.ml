open Core

(** A type parameter environment is a map from type parameter identifiers to sets of type parameter constraints *)
type t = Ty.Param_bounds.t Ty.Generic.Map.t [@@deriving compare, eq, sexp, show]

let empty : t = Ty.Generic.Map.empty
let is_empty t = Map.is_empty t

let bind (t : t) ty_param cstrs : t =
  (* Invariant: we should never rebind a type parameter *)
  Map.add_exn t ~key:ty_param ~data:cstrs
;;

let merge_disjoint_exn (t1 : t) (t2 : t) : t = Map.merge_disjoint_exn t1 t2

let meet t1 t2 =
  let f ~key:_ = function
    | `Left _ | `Right _ -> None
    | `Both (bounds_l, bounds_r) -> Some (Ty.Param_bounds.meet bounds_l bounds_r)
  in
  Map.merge t1 t2 ~f
;;

let find (t : t) id = Map.find t id
let map t ~f = Ty.Generic.Map.map t ~f
