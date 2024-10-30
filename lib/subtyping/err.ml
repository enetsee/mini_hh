open Core

module Minimal = struct
  type t =
    | Not_a_subtype of
        { ty_sub : Ty.t
        ; ty_super : Ty.t
        }
    | Disj of t list
    | Conj of t list
    | Multiple of t list
  [@@deriving compare, eq, sexp, variants]

  let rec pp ppf t =
    match t with
    | Not_a_subtype { ty_sub; ty_super } -> Fmt.(hovbox @@ pair ~sep:(any " </: ") Ty.pp Ty.pp) ppf (ty_sub, ty_super)
    | Disj ts -> Fmt.(hovbox @@ list ~sep:(any " | ") pp) ppf ts
    | Conj ts -> Fmt.(hovbox @@ list ~sep:(any " & ") pp) ppf ts
    | Multiple ts -> Fmt.(vbox @@ list ~sep:cut pp) ppf ts
  ;;
end

include Minimal
include Pretty.Make (Minimal)
