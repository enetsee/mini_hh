open Reporting

module Logical = struct
  type t =
    | And of Loc.t
    | Or of Loc.t
  [@@deriving eq, show, compare, sexp, variants]
end

type t = Logical of Logical.t [@@deriving eq, show, compare, sexp, variants]

let and_ loc = logical @@ Logical.and_ loc
let or_ loc = logical @@ Logical.or_ loc
