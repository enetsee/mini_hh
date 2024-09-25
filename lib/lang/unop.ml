open Reporting

module Logical = struct
  type t = Not of Loc.t [@@deriving eq, show, compare, sexp, variants]
end

type t = Logical of Logical.t [@@deriving eq, show, compare, sexp, variants]

let not loc = logical @@ Logical.not loc
