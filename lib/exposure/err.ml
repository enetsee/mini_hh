open Core

module Minimal = struct
  type t =
    | Unbound_ctor of Name.Ctor.t * Reporting.Prov.t
    | Invariant_param of Name.Ctor.t * Name.Ty_param.t * Reporting.Prov.t
  [@@deriving compare, equal, sexp, show, variants]
end

include Minimal
module Set = Set.Make (Minimal)
