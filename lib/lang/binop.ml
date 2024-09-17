module Logical = struct
  type t =
    | And
    | Or
  [@@deriving eq, show, compare, sexp]
end

type t = Logical of Logical.t [@@deriving eq, show, compare, sexp]
