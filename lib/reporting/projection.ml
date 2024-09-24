module Variance_dir = struct
  type t =
    | Cov
    | Contrav
  [@@deriving compare, eq, sexp, show, variants]
end

module Asymm = struct
  type t
end

module Symm = struct
  type t
end
