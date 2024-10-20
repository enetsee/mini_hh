open Core

type t = Ty.t Name.Tm_var.Map.t [@@deriving compare, eq, sexp, show]

let empty = Name.Tm_var.Map.empty
let bottom = empty
let find t local = Map.find t local
let is_bound t local = Option.is_some @@ find t local

let join t1 t2 ~prov =
  let f ~key:_ = function
    | `Left ty | `Right ty -> Some ty
    | `Both (ty1, ty2) -> Some (Ty.union ~prov [ ty1; ty2 ])
  in
  Map.merge t1 t2 ~f
;;

let meet t1 t2 ~prov =
  let f ~key:_ = function
    | `Left _ | `Right _ -> None
    | `Both (ty1, ty2) -> Some (Ty.inter ~prov [ ty1; ty2 ])
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
let map t ~f = Name.Tm_var.Map.map t ~f

let symm_diff (t1 : t) (t2 : t) =
  let k1 = Map.key_set t1
  and k2 = Map.key_set t2 in
  Set.symmetric_diff k1 k2
;;

module Refinement = struct
  (** A local refinement is a map from term variables names to formula over types*)
  type t = Ty.Refinement.t Name.Tm_var.Map.t [@@deriving compare, eq, sexp, show]

  let empty = Name.Tm_var.Map.empty
  let singleton nm ty_refinement = Name.Tm_var.Map.singleton nm ty_refinement
end
