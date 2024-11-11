open Core

module Minimal = struct
  type t =
    | Atom of Cstr.t
    | Conj of t list
    | Disj of t list
  [@@deriving compare, eq, sexp, variants]

  let true_ = conj []
  let false_ = disj []

  let rec pp ppf = function
    | Atom cstr -> Cstr.pp ppf cstr
    | Disj ts -> Fmt.(parens @@ hovbox @@ list ~sep:(any " || ") pp) ppf ts
    | Conj ts -> Fmt.(parens @@ hovbox @@ list ~sep:(any " && ") pp) ppf ts
  ;;
end

include Minimal
include Pretty.Make (Minimal)
