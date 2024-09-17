module Logical = struct
  type t = Not [@@deriving eq, show, compare, sexp]
end

type t = Logical of Logical.t [@@deriving eq, show, compare, sexp]
