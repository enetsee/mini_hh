module Logical = struct
  type t =
    | And
    | Or
  [@@deriving eq, show, compare, sexp, variants]
end

type t = Logical of Logical.t [@@deriving eq, show, compare, sexp, variants]

let and_ = logical @@ Logical.and_
let or_ = logical @@ Logical.or_
