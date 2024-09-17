open Core

module Minimal = struct
  type t =
    | Unbound_ctor of Identifier.Ctor.t
    | Invariant_param of Identifier.Ctor.t * Ty.Generic.t
  [@@deriving compare, equal, sexp, show, variants]
end

include Minimal
module Set = Set.Make (Minimal)
