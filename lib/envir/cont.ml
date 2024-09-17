open Core

module Cont_key = struct
  type t =
    | Next
    | Break
    | Continue
    | Exist
  [@@deriving eq, compare, sexp, show, variants]
end

module Cont_map = struct
  include Map.Make (Cont_key)

  let pp pp_a ppf t = Fmt.(vbox @@ list ~sep:cut @@ pair ~sep:(any " => ") Cont_key.pp pp_a) ppf @@ Map.to_alist t
end

type t = Local.t Cont_map.t [@@deriving compare, eq, sexp, show]

let singleton key data = Map.singleton key data

let join t1 t2 =
  let f ~key:_ = function
    | `Left v | `Right v -> Some v
    | `Both (vl, vr) -> Some (Local.join vl vr)
  in
  Map.merge t1 t2 ~f
;;
