open Core

module Refine_key = struct
  (** A type refinement key is either a term variable or a member property
      TODO(mjt) Add members *)
  type t = Local of Name.Tm_var.t [@@deriving compare, eq, sexp, show]
end

module Refine_map = struct
  include Map.Make (Refine_key)

  let pp pp_a ppf t = Fmt.(vbox @@ list ~sep:cut @@ pair ~sep:(any " => ") Refine_key.pp pp_a) ppf @@ Map.to_alist t
end

type t = Ty.Refinement.t Refine_map.t [@@deriving compare, eq, sexp, show]

let empty = Refine_map.empty
let find_local t local = Map.find t (Refine_key.Local local)

let join t1 t2 =
  let f ~key:_ = function
    | `Left rfn | `Right rfn -> Some rfn
    | `Both (rfn1, rfn2) -> Some (Ty.Refinement.join rfn1 rfn2)
  in
  Map.merge t1 t2 ~f
;;

let meet t1 t2 =
  let f ~key:_ = function
    | `Left _ | `Right _ -> None
    | `Both (rfn1, rfn2) -> Some (Ty.Refinement.meet rfn1 rfn2)
  in
  Map.merge t1 t2 ~f
;;

let cmp t = Refine_map.map t ~f:Ty.Refinement.cmp
let of_local local ty : t = Refine_map.singleton Refine_key.(Local local) @@ Ty.Refinement.pos ty
