open Core

(** A local environment is a map from term variables names to *)
type t = Ty.t Lang.Local.Map.t [@@deriving compare, eq, sexp, show]

let empty = Lang.Local.Map.empty
let bottom = empty
let find t local = Map.find t local
let is_bound t local = Option.is_some @@ find t local

let join t1 t2 =
  let f ~key:_ = function
    | `Left ty | `Right ty -> Some ty
    | `Both (ty1, ty2) -> Some (Ty.union [ ty1; ty2 ])
  in
  Map.merge t1 t2 ~f
;;

let meet t1 t2 =
  let f ~key:_ = function
    | `Left _ | `Right _ -> None
    | `Both (ty1, ty2) -> Some (Ty.inter [ ty1; ty2 ])
  in
  Map.merge t1 t2 ~f
;;

let merge_right t1 t2 : t =
  let f ~key:_ = function
    | `Left v | `Right v | `Both (_, v) -> Some v
  in
  Map.merge t1 t2 ~f
;;

let merge_disjoint_exn t1 t2 = Map.merge_disjoint_exn t1 t2
let bind_local t local ty = Map.update t local ~f:(fun _ -> ty)
let map t ~f = Lang.Local.Map.map t ~f

let symm_diff (t1 : t) (t2 : t) =
  let k1 = Map.key_set t1
  and k2 = Map.key_set t2 in
  Set.symmetric_diff k1 k2
;;
