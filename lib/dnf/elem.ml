module type S = sig
  type t [@@deriving eq, compare, sexp, show]
end
